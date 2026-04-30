import Automata.NatCDFA
import Automata.Partition


def nextPartition {a: Nat} (r: NatCDFA a) (p: Partition r.n) (b: Fin a): Partition r.n := {
  k := p.k,
  part := Vector.ofFn (fun s => p.part.get (r.δ s b))
}

theorem nextPartition_correct {a: Nat} {r: NatCDFA a} {p: Partition r.n} {b: Fin a}
  {i j: Fin r.n}:
    (nextPartition r p b).rel i j ↔ p.rel (r.δ i b) (r.δ j b) :=
  Partition.rel.eq_def _ _ _ ▸ Vector.get_ofFn ▸ Vector.get_ofFn ▸ Iff.refl _


def refinePartition {a: Nat} (r: NatCDFA a) (p: Partition r.n): Partition r.n :=
  let refined := Vector.ofFn (nextPartition r p)
  Partition.intersection (a + 1) (fun b => if lt: b < a then refined[b] else p)


theorem refinePartition_card_ge {a: Nat} {r: NatCDFA a} {p: Partition r.n}:
    p.card ≤ (refinePartition r p).card := Nat.le_trans
      (Nat.le_of_eq
        (Eq.symm (congrArg Partition.card (dite_cond_eq_false (eq_false fun lt => Nat.ne_of_lt lt rfl)))))
      (Partition.intersection_card_ge (Nat.lt_succ_self a))


theorem refinePartition_of_card_eq {a: Nat} {r: NatCDFA a} {p: Partition r.n}:
    p.card = (refinePartition r p).card → p.rel = (refinePartition r p).rel :=
  fun h =>
    let refined := Vector.ofFn (nextPartition r p)
    let f := fun b => if lt: b < a then refined[b] else p
    have eq: f a = p := dite_cond_eq_false (eq_false fun lt => Nat.ne_of_lt lt rfl)
    (congrArg Partition.rel eq.symm).trans
      (Partition.of_intersection_card_eq (f := f) (Nat.lt_succ_self a) (eq ▸ h))


theorem refinePartition_normalized {a: Nat} {r: NatCDFA a} {p: Partition r.n}:
    (refinePartition r p).normalized :=
  Partition.intersection_normalized


theorem refinePartition_correct {a: Nat} {r: NatCDFA a} {p: Partition r.n} {i j: Fin r.n}:
    (refinePartition r p).rel i j ↔ (∀ b: Fin a, p.rel (r.δ i b) (r.δ j b)) ∧ p.rel i j :=
  let refined := Vector.ofFn (nextPartition r p)
  let f := fun b => if lt: b < a then refined[b] else p
  have eqa: f a = p := dite_cond_eq_false (eq_false fun lt => Nat.ne_of_lt lt rfl)
  have eqb (b: Fin a): f b = nextPartition r p b :=
    (dite_cond_eq_true (eq_true b.isLt)).trans (Vector.getElem_ofFn b.isLt)
  Iff.trans Partition.intersection_correct ⟨
    fun h => ⟨
      fun b => nextPartition_correct.mp ((eqb b) ▸ (h b.val (Nat.lt_succ_of_lt b.isLt))),
      eqa ▸ (h a (Nat.lt_succ_self a))
    ⟩,
    fun ⟨relb, rela⟩ b hb => match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hb) with
      | .inl eq =>
        Eq.subst (motive := fun w: Partition r.n => w.rel i j) ((congrArg f eq) ▸ eqa).symm rela
      | .inr lt =>
        have relb := nextPartition_correct.mpr (relb ⟨b, lt⟩)
        Eq.subst (motive := fun w: Partition r.n => w.rel i j) (eqb ⟨b, lt⟩).symm relb
  ⟩


def terminalPartition {a: Nat} (r: NatCDFA a): Partition r.n := Partition.predPartNormalized r.t


theorem terminalPartition_correct {a: Nat} {r: NatCDFA a} {i j: Fin r.n}:
    (terminalPartition r).rel i j ↔ r.t i = r.t j :=
  Partition.predPartNormalized_correct


theorem terminalPartition_normalized {a: Nat} {r: NatCDFA a}: (terminalPartition r).normalized :=
  Partition.predPartNormalized_normalized


theorem computeMooreFrom_decreasing {a: Nat} {r: NatCDFA a} {p: Partition r.n}
  (hn: p.normalized) (h: (refinePartition r p).k ≠ p.k) :
    r.n - (refinePartition r p).card < r.n - p.card :=
  Nat.lt_of_le_of_ne
    (Nat.sub_le_sub_left refinePartition_card_ge r.n)
    (fun eq =>
      have card_eq: (refinePartition r p).card = p.card :=
        Nat.sub_sub_self (Partition.card_le_n) (m := p.card) ▸
        Nat.sub_sub_self (Partition.card_le_n) (m := (refinePartition _ _).card) ▸
        (congrArg (r.n - ·) eq)
      have k_eq: (refinePartition r p).k = p.k :=
        Partition.card_normalized hn ▸
        Partition.card_normalized refinePartition_normalized ▸
        card_eq
      h k_eq)


def computeMooreFrom {a: Nat} (r: NatCDFA a) (p: Partition r.n) (_: p.normalized): Partition r.n :=
  let new := refinePartition r p
  if new.k = p.k then
    p
  else computeMooreFrom r new refinePartition_normalized
  termination_by r.n - p.card
  decreasing_by case _ hn h => exact computeMooreFrom_decreasing hn h


theorem computeMooreFrom_correct1 {a: Nat} {r: NatCDFA a} {p: Partition r.n} {hn: p.normalized}
  {i j: Fin r.n} (h: ∀ w: List (Fin a), p.rel (r.advanceFrom i w) (r.advanceFrom j w)):
    (computeMooreFrom r p hn).rel i j :=
  computeMooreFrom.eq_def r p hn ▸
    iteInduction (motive := fun w: Partition r.n => w.rel i j)
      (fun _ => h []) (fun _ =>
        computeMooreFrom_correct1 (fun w => refinePartition_correct.mpr ⟨
          fun b => NatCDFA.advanceFrom_concat ▸ NatCDFA.advanceFrom_concat ▸  h (w ++ [b]), h w
        ⟩)
      )
  termination_by r.n - p.card
  decreasing_by case _ _ h => exact computeMooreFrom_decreasing hn h


theorem computeMooreFrom_correct2 {a: Nat} {r: NatCDFA a} {p: Partition r.n} {hn: p.normalized} {i j: Fin r.n}:
    (computeMooreFrom r p hn).rel i j → p.rel i j :=
  computeMooreFrom.eq_def r p hn ▸
    iteInduction (motive := fun w: Partition r.n => w.rel i j → p.rel i j) (fun _ => id)
      (fun _ rel => (refinePartition_correct.mp (computeMooreFrom_correct2 rel)).right)
  termination_by r.n - p.card
  decreasing_by case _ _ h => exact computeMooreFrom_decreasing hn h


theorem computeMooreFrom_fix_k {a: Nat} {r: NatCDFA a} {p: Partition r.n} {hn: p.normalized}:
    (computeMooreFrom r p hn).k = (refinePartition r (computeMooreFrom r p hn)).k :=
  computeMooreFrom.eq_def r p hn ▸
    iteInduction (motive := fun w: Partition r.n => w.k = (refinePartition r w).k)
      Eq.symm (fun _ => computeMooreFrom_fix_k)
  termination_by r.n - p.card
  decreasing_by case _ _ h => exact computeMooreFrom_decreasing hn h


theorem computeMooreFrom_normalized {a: Nat} {r: NatCDFA a} {p: Partition r.n} {hn: p.normalized}:
    (computeMooreFrom r p hn).normalized :=
  computeMooreFrom.eq_def r p hn ▸
    iteInduction (motive := fun w: Partition r.n => w.normalized) (fun _ => hn)
      (fun _ => computeMooreFrom_normalized)
  termination_by r.n - p.card
  decreasing_by case _ _ h => exact computeMooreFrom_decreasing hn h


def computeMoore {a: Nat} (r: NatCDFA a): Partition r.n :=
  computeMooreFrom r (terminalPartition r) terminalPartition_normalized


theorem computeMoore_correct1 {a: Nat} {r: NatCDFA a} {i j: Fin r.n} (h: r.acceptsFrom i = r.acceptsFrom j):
    (computeMoore r).rel i j :=
  computeMooreFrom_correct1 (fun w => Partition.predPartNormalized_correct.mpr (congrFun h w))


theorem computeMoore_fix_k {a: Nat} {r: NatCDFA a}:
    (computeMoore r).k = (refinePartition r (computeMoore r)).k :=
  computeMooreFrom_fix_k


theorem computeMoore_fix {a: Nat} {r: NatCDFA a}:
    (computeMoore r).rel = (refinePartition r (computeMoore r)).rel :=
  refinePartition_of_card_eq (
    Partition.card_normalized computeMooreFrom_normalized ▸
    Partition.card_normalized refinePartition_normalized ▸
    computeMoore_fix_k
  )


theorem computeMoore_correct2 {a: Nat} {r: NatCDFA a} {i j: Fin r.n} (h: (computeMoore r).rel i j):
    {l: List (Fin a)} → r.acceptsFrom i l = r.acceptsFrom j l
  | [] => terminalPartition_correct.mp (computeMooreFrom_correct2 h)
  | b::_ => computeMoore_correct2
    ((refinePartition_correct.mp (Eq.subst (motive := fun w => w i j) computeMoore_fix h)).left b)


theorem computeMoore_correct {a: Nat} {r: NatCDFA a} {i j: Fin r.n}:
    (computeMoore r).rel i j ↔ r.acceptsFrom i = r.acceptsFrom j :=
  ⟨
    fun h => funext (fun _ => computeMoore_correct2 h),
    computeMoore_correct1
  ⟩
