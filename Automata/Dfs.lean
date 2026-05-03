import Automata.NatCDFA
import Automata.RadixSort --Just for utility functions, to clean up later

/-
DFS to find a "state morphism" (which does not necessarily map terminal states to terminal states)
-/
def Vector.cNone {α} {n: Nat} (v: Vector (Option α) n) := v.countP Option.isNone


theorem Vector.cNone_set {α} {n: Nat} {v: Vector (Option α) n} {i: Fin n} {x: α}
  (h: v.get i = none):
    (v.set i x).cNone + 1 = v.cNone :=
  have cond: v[i.val].isNone = true := Option.isNone_iff_eq_none.mpr h
  have le: v.countP Option.isNone ≥ 1 := Nat.one_le_of_lt (Vector.countP_pos_iff.mpr
    ⟨v.get i, Vector.getElem_mem _, Option.isNone_iff_eq_none.mpr h⟩)
  (congrArg (· + 1) (Vector.countP_set i.isLt)).trans (
    ite_cond_eq_true _ _ (eq_true cond) ▸ Nat.sub_add_comm le ▸
    (Nat.sub_add_cancel (Nat.le_add_right_of_le le)).symm ▸ rfl)


def dfsFindMorphismFrom {a: Nat} (r s: NatCDFA a) (p: Fin r.n) (q: Fin s.n)
  (asgn: Vector (Option (Fin s.n)) r.n):
    Nat → Option (Vector (Option (Fin s.n)) r.n)
  | 0 => none
  | fuel + 1 =>
    match asgn.get p with
    | none => Fin.foldlM a
      (fun acc b => dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) acc fuel)
      (asgn.set p (some q))
    | some q' => if q' = q then some asgn else none


theorem Fin.foldlM_induction {α m} [Monad m] [LawfulMonad m] {n: Nat} (motive: m α → Nat → Prop)
  {init: α} (h0: motive (pure init) 0) {f: α → Fin n → m α}
  (hr: ∀ (a: m α) (i: Fin n), motive a i.val → motive (a >>= (f · i)) i.val.succ):
    motive (Fin.foldlM n f init) n :=
  match n with
  | 0 =>  (congrFun (Fin.foldlM_zero f) init).symm.subst (motive := fun w => motive w 0) h0
  | n + 1 =>
    have hrec: motive (Fin.foldlM n (fun a i => f a i.castSucc) init) n :=
      Fin.foldlM_induction _ h0 (fun a i ha => hr a i.castSucc ha)
    Fin.foldlM_succ_last (m := m) _ ▸ hr _ (last n) hrec


theorem Vector.get_set_self {α} {n: Nat} {v: Vector α n} {i: Fin n} {a: α}:
    (v.set i a).get i = a :=
  Vector.getElem_set_self i.isLt


theorem Vector.get_set_of_ne {α} {n: Nat} {v: Vector α n} {i j: Fin n} {a: α} (h: i ≠ j):
    (v.set i a).get j = v.get j :=
  Vector.getElem_set_ne i.isLt j.isLt (Fin.val_ne_of_ne h)


theorem dfsFindMorphismFrom_preserves_some {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {asgn: Vector (Option (Fin s.n)) r.n} {i: Fin r.n} {j: Fin s.n} (h: asgn.get i = some j):
    {fuel: Nat} → (dfsFindMorphismFrom r s p q asgn fuel).all (fun w => w.get i = some j)
  | 0 => rfl
  | fuel + 1 =>
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        Fin.foldlM_induction (fun (w: Option _) _ => w.all _ = true)
          (have ne: p ≠ i := fun eq2 => Option.some_ne_none j (h.symm.trans (eq2 ▸ eq))
            have concl: (asgn.set p (some q)).get i = some j :=
              (Vector.get_set_of_ne ne).trans h
            Option.pure_apply ▸ decide_eq_true concl)
          (fun acc b hrec =>
            match acc with
            | none => rfl
            | some acc => dfsFindMorphismFrom_preserves_some (of_decide_eq_true hrec))
    | some q' => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Option _ => w.all _ = true)
          (fun _ => decide_eq_true h) (fun _ => rfl)


theorem dfsFindMorphismFrom_step {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {asgn: Vector (Option (Fin s.n)) r.n}:
    {fuel: Nat} → (dfsFindMorphismFrom r s p q asgn fuel).all (fun w => w.get p = some q)
  | 0 => rfl
  | _ + 1 =>
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        Fin.foldlM_induction (fun (w: Option _) _ => w.all _ = true)
          (Option.pure_apply ▸ decide_eq_true Vector.get_set_self)
          (fun acc _ hrec =>
            match acc with
            | none => rfl
            | some _ => dfsFindMorphismFrom_preserves_some (of_decide_eq_true hrec)
          )
    | some _ => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Option _ => w.all _ = true)
          (fun eq2 => decide_eq_true (eq2 ▸ eq)) (fun _ => rfl)


theorem Option.all_mp {α} {p q: α → Bool} {o: Option α} (h1: o.all p) (h2: ∀ a: α, p a → q a): o.all q :=
  match o with
  | none => rfl
  | some a => h2 a h1


theorem dfsFindMorphismFrom_cNone {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {asgn: Vector (Option (Fin s.n)) r.n}:
    {fuel: Nat} → (dfsFindMorphismFrom r s p q asgn fuel).all (fun w => w.cNone ≤ asgn.cNone)
  | 0 => rfl
  | fuel + 1 =>
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        Fin.foldlM_induction (fun (w: Option _) _ => w.all _ = true)
          (Option.pure_def ▸ decide_eq_true (Nat.le_of_add_le_add_right (b := 1)
            (Vector.cNone_set eq ▸ Nat.le_succ asgn.cNone)))
          (fun acc b hrec => match acc with
            | none => rfl
            | some acc =>
              have hrec2: (dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) acc fuel).all
                  (fun w => w.cNone ≤ acc.cNone) := dfsFindMorphismFrom_cNone
              Option.all_mp hrec2 (fun _ hacc2 => decide_eq_true (Nat.le_trans
                  (of_decide_eq_true hacc2) (of_decide_eq_true hrec)))
          )
    | some _ => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Option _ => w.all _ = true)
          (fun _ => decide_eq_true (Nat.le_refl asgn.cNone)) (fun _ => rfl)


def stateMorphism {a: Nat} (r s: NatCDFA a) (f: Fin r.n → Fin s.n): Prop :=
  ∀ l: List (Fin a), f (r.advance l) = s.advance l


theorem dfsFindMorphismFrom_tracks_morphism {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {asgn: Vector (Option (Fin s.n)) r.n} (ht2: ∃ l, p = r.advance l ∧ q = s.advance l) (f: Fin r.n → Fin s.n)
  (h: stateMorphism r s f) (ht: ∀ i: Fin r.n, (asgn.get i).all (· = f i))
  {fuel: Nat} (hf: fuel > asgn.cNone):
    (dfsFindMorphismFrom r s p q asgn fuel).any (fun acc => ∀ i: Fin r.n, (acc.get i).all (· = f i)) :=
  match fuel with
  | 0 => False.elim (Nat.not_lt_zero asgn.cNone hf)
  | fuel + 1 =>
    have ⟨l, eql1, eql2⟩ := ht2
    have ht2_eq: f p = q := eql1 ▸ eql2 ▸ (h l)
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        (Fin.foldlM_induction
          (fun (w: Option (Vector (Option (Fin s.n)) r.n)) _ =>
            w.any (fun acc => ∀ i: Fin r.n, (acc.get i).all (· = f i)) = true
            ∧ w.all (fun z => fuel > z.cNone)
          )
          ⟨
            Option.pure_def ▸ decide_eq_true (fun i => if eq2: i = p then
              eq2 ▸ Vector.get_set_self ▸ decide_eq_true (eq2 ▸ ht2_eq.symm)
            else
              (Vector.get_set_of_ne (Ne.symm eq2)).symm ▸ ht i),
            Option.pure_def ▸ decide_eq_true (Nat.lt_of_add_lt_add_right (Vector.cNone_set eq ▸ hf))
          ⟩
          (fun acc b ⟨hrec, hf⟩ =>
            match acc with
            | none => ⟨hrec, hf⟩
            | some acc => ⟨
              have hrec: ∀ i: Fin r.n, (acc.get i).all (· = f i) := of_decide_eq_true hrec
              dfsFindMorphismFrom_tracks_morphism
                ⟨l ++ [b],
                  (congrArg (fun w => r.δ w b) eql1).trans NatCDFA.advance_concat.symm,
                  (congrArg (fun w => s.δ w b) eql2).trans NatCDFA.advance_concat.symm
                ⟩
                f h hrec (of_decide_eq_true hf),
              Option.all_mp dfsFindMorphismFrom_cNone (fun _ hacc2 =>
                decide_eq_true (Nat.lt_of_le_of_lt (of_decide_eq_true hacc2) (of_decide_eq_true hf)))
          ⟩)
        ).left
    | some q' => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Option _ => w.any _ = true)
          (fun _ => decide_eq_true ht)
          (fun ne => False.elim (
            have eq2: q' = f p := of_decide_eq_true
              (Eq.subst (motive := fun w: Option (Fin s.n) => w.all _) eq (ht p))
            ne (eq2.trans ht2_eq)
          ))


theorem dfsFindMorphismFrom_accessible {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {asgn: Vector (Option (Fin s.n)) r.n} (ht: ∃ l, p = r.advance l ∧ q = s.advance l)
  {i: Fin r.n} (h: ∀ l: List (Fin a), i ≠ r.advance l):
    {fuel: Nat} → (dfsFindMorphismFrom r s p q asgn fuel).all (fun acc => acc.get i = none)
  | 0 => rfl
  | fuel + 1 => sorry


def Option.allP {α} (p: α → Prop): (o: Option α) → Prop
  | none => True
  | some a => p a


theorem Option.allP_mp {α} {p q: α → Prop} {o: Option α} (h1: o.allP p) (h2: ∀ a: α, p a → q a): o.allP q :=
  match o with
  | none => True.intro
  | some a => h2 a h1


theorem Option.allP_all {α} {p: α → Bool}: {o: Option α} → o.all p = true ↔ o.allP (fun a => p a = true)
  | none => ⟨fun _ => True.intro, fun _ => rfl⟩
  | some _ => ⟨id, id⟩


theorem Option.allP_and {α} {p q: α → Prop}: {o: Option α} → o.allP p ∧ o.allP q ↔ o.allP (fun a => p a ∧ q a)
  | none => ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩
  | some _ => ⟨id, id⟩


theorem Option.allP_forall {α} {ι} {p: ι → α → Prop}:
    {o: Option α} → (∀ i, o.allP (p i)) ↔ (o.allP (fun a => ∀ i, p i a))
  | none => ⟨fun _ => True.intro, fun _ _ => True.intro⟩
  | some _ => ⟨id, id⟩


theorem Option.allP_imp {α} {c: Prop} {p: α → Prop}:
    {o: Option α} → (c → o.allP p) ↔ (o.allP (fun a => c → p a))
  | none => ⟨fun _ => True.intro, fun _ _ => True.intro⟩
  | some _ => ⟨id, id⟩


def morphismInvariant {a: Nat} (r s: NatCDFA a)
  (grey: List (Fin r.n)) (acc: Vector (Option (Fin s.n)) r.n): Prop :=
    ∀ p: Fin r.n, p ∉ grey → (acc.get p).allP (fun q => ∀ b: Fin a, acc.get (r.δ p b) = some (s.δ q b))


--The big ugly theorem - the annoying part is managing partially explored (grey) nodes.
theorem dfsFindMorphismFrom_morphism {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {asgn: Vector (Option (Fin s.n)) r.n} (grey: List (Fin r.n)) (hm: morphismInvariant r s grey asgn):
    {fuel: Nat} → (dfsFindMorphismFrom r s p q asgn fuel).allP (morphismInvariant r s grey)
  | 0 => True.intro
  | fuel + 1 =>
    match eq: asgn.get p with
    | none =>
        let motive (acc: Option (Vector (Option (Fin s.n)) r.n)) (c: Nat): Prop := acc.allP (fun acc2 =>
          morphismInvariant r s (p::grey) acc2
          ∧ (∀ b: Fin a, b.val < c → acc2.get (r.δ p b) = some (s.δ q b))
          ∧ (acc2.get p = some q)
        )
        have ind: motive (Fin.foldlM a
            (fun acc b => dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) acc fuel)
            (asgn.set p (some q))) a :=
          Fin.foldlM_induction motive
            (Option.pure_def ▸ ⟨
              fun i hi =>
                have ne: p ≠ i := fun eq2 => hi (eq2 ▸ List.mem_cons_self)
                have nmem: i ∉ grey := fun mem => hi (List.mem_cons_of_mem _ mem)
                (Vector.get_set_of_ne ne).symm ▸ (Option.allP_mp (hm i nmem) (fun j hj b =>
                  have ne2: p ≠ r.δ i b := fun eq2 => (Option.some_ne_none (s.δ j b))
                    ((hj b).symm.trans (eq2 ▸ eq))
                  (Vector.get_set_of_ne ne2).symm ▸ hj b)),
              fun b hb => False.elim (Nat.not_lt_zero b hb),
              Vector.get_set_self,
            ⟩)
            (fun acc b hrec => match acc with
              | none => True.intro
              | some acc => (
                  have prev: (dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) acc fuel).allP
                      (fun acc2 => ∀ c: Fin a, c.val < b → acc2.get (r.δ p c) = some (s.δ q c)) :=
                    Option.allP_forall.mp (fun c => Option.allP_imp.mp (fun hc =>
                      have prev: (dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) acc fuel).all
                          (fun acc2 => acc2.get (r.δ p c) = some (s.δ q c)) :=
                        dfsFindMorphismFrom_preserves_some (hrec.right.left c hc)
                      Option.allP_mp (Option.allP_all.mp prev) (fun acc2 => of_decide_eq_true)
                    ))
                  Option.allP_mp (Option.allP_and.mp ⟨
                    dfsFindMorphismFrom_morphism (p::grey) hrec.left,
                    Option.allP_and.mp ⟨
                      prev,
                      Option.allP_and.mp ⟨
                        Option.allP_all.mp dfsFindMorphismFrom_step,
                        Option.allP_all.mp (dfsFindMorphismFrom_preserves_some hrec.right.right)
                      ⟩
                    ⟩
                  ⟩) (fun acc2 ⟨hrec1, hrec2, hrec3, hrec4⟩ => ⟨
                      hrec1,
                      (fun c hc => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with
                        | .inl lt => hrec2 c lt
                        | .inr eq2 => (Fin.eq_of_val_eq eq2) ▸ of_decide_eq_true hrec3
                      ),
                      of_decide_eq_true hrec4,
                    ⟩
                  )
                )
            )
        dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
          Option.allP_mp ind (fun acc hacc p2 hp2 =>
            if eq2: p2 = p then
              have rep: acc.get p2 = some q := eq2 ▸ hacc.right.right
              rep ▸ fun b => eq2 ▸ hacc.right.left b b.isLt
            else
              hacc.left p2 (fun mem => match List.mem_cons.mp mem with
                | .inl eq3 => eq2 eq3
                | .inr mem2 => hp2 mem2
              )
          )
    | some q' => dfsFindMorphismFrom.eq_def r s p q asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Option _ => w.allP _)
          (fun _ =>  hm) (fun _ => True.intro)


def dfsFindMorphism {a: Nat} (r s: NatCDFA a): Option (Vector (Fin s.n) r.n) :=
    (dfsFindMorphismFrom r s r.i s.i (Vector.replicate r.n none) (r.n + 1)).map (Vector.map (fun o => o.getD s.i))


def Option.anyP {α} (p: α → Prop): (o: Option α) → Prop
  | none => True
  | some a => p a


theorem Option.allP_map {α β} {f: α → β} {p: β → Prop}:
    {o: Option α} → o.allP (p ∘ f) ↔ (o.map f).allP p
  | none => ⟨fun _ => True.intro, fun _ => True.intro⟩
  | some _ => ⟨id, id⟩


theorem Vector.get_map {α β} {n: Nat} {v: Vector α n} {f: α → β} {i: Fin n}:
    (v.map f).get i = f (v.get i) :=
  Vector.getElem_map f i.isLt


theorem dfsFindMorphism_is_morphism {a: Nat} {r s: NatCDFA a}:
    (dfsFindMorphism r s).allP (fun v => stateMorphism r s v.get) :=
  Option.allP_map.mp (Option.allP_mp
    (Option.allP_and.mp ⟨
      dfsFindMorphismFrom_morphism [] (fun p _ => Vector.get_replicate ▸ True.intro),
      Option.allP_all.mp dfsFindMorphismFrom_step
    ⟩)
    (fun v ⟨hv1, hv2⟩ => Function.comp_apply ▸ fun l =>
      let rec propagate (u: List (Fin a)): v.get (r.advance u) = some (s.advance u) :=
        match List.eq_nil_or_concat u with
        | .inl eq_nil => eq_nil ▸ of_decide_eq_true hv2 ▸ rfl
        | .inr ⟨start, b, eq_cat⟩ =>
          have tr := hv1 (r.advance start) List.not_mem_nil
          have hrec := propagate start
          have concl: v.get (r.δ (r.advance start) b) = some (s.δ (s.advance start) b) := ((hrec ▸ tr) b)
          eq_cat ▸ List.concat_eq_append ▸
            NatCDFA.advance_concat (r := s) ▸ NatCDFA.advance_concat (r := r) ▸ concl
        termination_by u.length
      Vector.get_map ▸ propagate l ▸ rfl
    ))


theorem Option.anyP_of_allP_isSome {α} {p: α → Prop}:
    {o: Option α} → o.allP p → o.isSome → o.anyP p
  | none => fun _ h => False.elim (nomatch Option.isSome_none ▸ h)
  | some _ => fun h _ => h


theorem dfsFindMorphism_finds_morphism {a: Nat} {r s: NatCDFA a} (h: ∃ f, stateMorphism r s f):
    (dfsFindMorphism r s).anyP (fun v => stateMorphism r s v.get) :=
  have ⟨f, hf⟩ := h
  Option.anyP_of_allP_isSome dfsFindMorphism_is_morphism (
    Option.isSome_map.symm ▸ Option.isSome_of_any (dfsFindMorphismFrom_tracks_morphism
      ⟨[], rfl, rfl⟩ f hf (fun _ => Vector.get_replicate ▸ rfl) (Nat.lt_succ_of_le Vector.countP_le_size)
    )
  )


/-
Construction over the previous functions to check for the existence of a morphism
-/
