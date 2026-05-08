module

import AutoKchp.Dedup
public import AutoKchp.Counting
import AutoKchp.Util

public structure Partition (n: Nat) where
  k: Nat
  part: Vector (Fin k) n


namespace Partition

@[expose]
public def rel {n: Nat} (p: Partition n):
    Fin n → Fin n → Prop :=
  fun i j => p.part.get i = p.part.get j


theorem zero_lt {n: Nat} {p: Partition n} (h: n ≠ 0):
    0 < p.k :=
  Nat.zero_lt_of_lt (p.part.get ⟨0, Nat.zero_lt_of_ne_zero h⟩).isLt


public def intersection {n: Nat} (s: Nat) (f: Nat → Partition n): Partition n :=
  if eq: n = 0 then
    {
      k := 0,
      part := Vector.mk #[] eq.symm
    }
  else
    let f := fun i r => (f r).part.getD i ⟨0, zero_lt eq⟩
    let result := radixDedup f n s
    {
      k := result.snd,
      part := Vector.mk
        (result.fst.pmap (fun a ha => ⟨a, radixDedup_lt ha⟩) (fun _ => id))
        (Eq.trans Array.size_pmap size_radixDedup)
    }


theorem intersection_nnnz {n: Nat} {s: Nat} {f: Nat → Partition n} (h: n ≠ 0):
    (intersection s f).part.toArray.map Fin.val =
    (radixDedup (fun i r => (f r).part.getD i ⟨0, zero_lt h⟩) n s).fst :=
  let rdd: Array Nat :=
    (radixDedup (fun i r => (f r).part.getD i ⟨0, zero_lt h⟩) n s).fst
  let k: Nat :=
    (radixDedup (fun i r => (f r).part.getD i ⟨0, zero_lt h⟩) n s).snd
  have concl: (rdd.pmap (α := Nat) (β := Fin k)
        (fun a ha => ⟨a, radixDedup_lt ha⟩) (fun _ => id)
      ).map Fin.val = rdd :=
    Array.map_pmap _ ▸ Array.pmap_eq_self.mpr (fun _ _ => Fin.val_mk _)
  intersection.eq_def _ _ ▸ dite_cond_eq_false (eq_false h) ▸ concl


theorem intersection_nnnz_k {n: Nat} {s: Nat} {f: Nat → Partition n} (h: n ≠ 0):
    (intersection s f).k =
    (radixDedup (fun i r => (f r).part.getD i ⟨0, zero_lt h⟩) n s).snd :=
  congrArg k (dite_cond_eq_false (eq_false h))


theorem rel_get_simpl {n: Nat} {p: Partition n} {i j: Fin n}:
    p.rel i j ↔ (p.part.toArray.map Fin.val)[i.val] = (p.part.toArray.map Fin.val)[j.val] :=
  Array.getElem_map Fin.val _ (i := i) ▸ Array.getElem_map Fin.val _ (i := j) ▸
    Fin.val_inj.symm


public theorem intersection_correct {n: Nat} {s: Nat} {f: Nat → Partition n} {i j: Fin n}:
    (intersection s f).rel i j ↔ ∀ r: Nat, r < s → (f r).rel i j :=
  if eq: n = 0 then
    False.elim (Nat.not_lt_zero i (eq ▸ i.isLt))
  else
    let fin_zero (r: Nat): Fin (f r).k := ⟨0, zero_lt eq⟩
    have size_eq: (radixDedup (fun i r => (f r).part.getD i (fin_zero r)) n s).fst.size = n :=
      size_radixDedup
    have simpl: (intersection s f).rel i j ↔
        (radixDedup (fun i r => (f r).part.getD i (fin_zero r)) n s).fst[i.val] =
        (radixDedup (fun i r => (f r).part.getD i (fin_zero r)) n s).fst[j.val] :=
      Iff.trans rel_get_simpl (
        (getElem_congr_coll (idx := Nat) (i := i.val) (intersection_nnnz eq)).symm ▸
        (getElem_congr_coll (idx := Nat) (i := j.val) (intersection_nnnz eq)).symm ▸
        Iff.refl _)
    have getD_eq_i (r: Nat): (f r).part.get i = (f r).part.getD i (fin_zero r) :=
      Array.getElem_eq_getD _
    have getD_eq_j (r: Nat): (f r).part.get j = (f r).part.getD j (fin_zero r) :=
      Array.getElem_eq_getD _
    Iff.trans simpl (Iff.trans
      (radixDedup_correct i.isLt j.isLt)
      ⟨
        fun h r hr => (rel.eq_def _ i j) ▸ (getD_eq_i r) ▸ (getD_eq_j r) ▸ h r hr,
        fun h r hr =>
          have concl: (f r).part.getD ↑i (fin_zero r) = (f r).part.getD ↑j (fin_zero r) :=
            (getD_eq_j r).symm ▸ (getD_eq_i r).symm ▸ h r hr
          concl
      ⟩)


@[expose]
public def normalized {n: Nat} (p: Partition n): Prop := ∀ i: Fin p.k, i ∈ p.part


public theorem intersection_normalized {n: Nat} {s: Nat} {f: Nat → Partition n}:
    (intersection s f).normalized := fun i =>
  if eq: n = 0 then
    have k_eq: (intersection s f).k = 0 :=
      Eq.trans (congrArg k (dite_cond_eq_true (eq_true eq))) rfl
    False.elim (Nat.not_lt_zero i.val (Nat.lt_of_lt_of_eq i.isLt k_eq))
  else
    have mem: i.val ∈ (intersection s f).part.toArray.map Fin.val :=
    have h: i.val < (radixDedup (fun i r => (f r).part.getD i ⟨0, _⟩) n s).snd :=
      Nat.lt_of_lt_of_eq i.isLt (intersection_nnnz_k eq)
    intersection_nnnz eq ▸ radixDedup_normalized h
    have ⟨_, ha, eqa⟩ := Array.mem_map.mp mem
    (Vector.mem_toArray_iff i _).mp ((Fin.val_inj.mp eqa) ▸ ha)


@[expose]
public def card {n: Nat} (p: Partition n): Nat := (p.part.map Fin.val).toList.card


public theorem card_normalized {n: Nat} {p: Partition n} (h: p.normalized):
    p.card = p.k :=
  have le1: p.card ≤ p.k := List.card_at_most (fun _ hi =>
    have ⟨a, _, eq⟩ := Vector.mem_map.mp (Vector.mem_toList_iff.mp hi); eq ▸ a.isLt)
  have le2: p.k ≤ p.card := List.card_at_least (fun i hi =>
    Vector.mem_toList_iff.mpr (Vector.mem_map.mpr ⟨⟨i, hi⟩, h _, rfl⟩))
  Nat.le_antisymm le1 le2


public theorem card_le_n {n: Nat} {p: Partition n}:
    p.card ≤ n :=
  Nat.le_trans List.card_le_length (Nat.le_of_eq Vector.length_toList)

end Partition

/-
Lemmas to prove that card is an antitone function of rel
-/
def card_rel (r: Nat → Nat → Bool): Nat → Nat
  | 0 => 0
  | n + 1 => if ∃ i: Nat, i < n ∧ r i n then card_rel r n else (card_rel r n) + 1


theorem card_rel_anti {r₁ r₂: Nat → Nat → Bool} (h: ∀ i j, r₁ i j → r₂ i j):
    {n: Nat} → card_rel r₂ n ≤ card_rel r₁ n
  | 0 => Nat.le_refl 0
  | n + 1 => have hrec: card_rel r₂ n ≤ card_rel r₁ n := card_rel_anti h
    iteInduction (motive := fun w => card_rel r₂ (n + 1) ≤ w)
      (fun ⟨i, hi, reli⟩ => iteInduction (motive := fun w => w ≤ card_rel r₁ n)
        (fun _ => hrec) (fun ndup2 => False.elim (ndup2 ⟨i, hi, h i n reli⟩)))
      (fun _ => iteInduction (motive := fun w => w ≤ card_rel r₁ n + 1)
        (fun _ => Nat.le_succ_of_le hrec) (fun _ => Nat.succ_le_succ hrec))


structure BEquivalence (r: Nat → Nat → Bool): Prop where
  refl: ∀ a: Nat, r a a
  symm: ∀ a b: Nat, r a b → r b a
  trans: ∀ a b c: Nat, r a b → r b c → r a c


theorem card_rel_anti_eq {r₁ r₂: Nat → Nat → Bool} (h: ∀ i j, r₁ i j → r₂ i j)
    (he1: BEquivalence r₁) (he2: BEquivalence r₂):
    {n: Nat} → card_rel r₂ n = card_rel r₁ n → ∀ i j, i < n → j < n → r₂ i j → r₁ i j
  | 0 => fun _ i _ hi => False.elim (Nat.not_lt_zero i hi)
  | n + 1 => fun eq =>
    have cond_eq: (∃ i: Nat, i < n ∧ r₂ i n) ↔ (∃ i: Nat, i < n ∧ r₁ i n) :=
      ⟨
        fun ex =>
          if ex2: ∃ i: Nat, i < n ∧ r₁ i n then
            ex2
          else
            have eq: card_rel r₂ n = card_rel r₁ n + 1 :=
              ((ite_cond_eq_true _ _ (eq_true ex)).symm.trans eq).trans
              (ite_cond_eq_false _ _ (eq_false ex2))
            have le: card_rel r₂ n ≤ card_rel r₁ n := card_rel_anti h
            False.elim (Nat.not_add_one_le_self (card_rel r₁ n) (eq ▸ le)),
        fun ⟨i, hi, rel⟩ => ⟨i, hi, h i n rel⟩
      ⟩
    have rec_card_eq: card_rel r₂ n = card_rel r₁ n :=
      if ex: ∃ i: Nat, i < n ∧ r₂ i n then
        (ite_cond_eq_true _ _ (eq_true ex)).symm.trans
          (eq.trans (ite_cond_eq_true _ _ (eq_true (cond_eq.mp ex))))
      else
        have succ_eq: card_rel r₂ n + 1 = card_rel r₁ n + 1 :=
          (ite_cond_eq_false _ _ (eq_false ex)).symm.trans
            (eq.trans (ite_cond_eq_false _ _ (eq_false (fun ex2 => ex (cond_eq.mpr ex2)))))
        Nat.add_right_cancel succ_eq
    have hrec := card_rel_anti_eq h he1 he2 rec_card_eq
    fun i j hi hj rel =>
      if eqi: i = n then
        if eqj: j = n then
          eqi ▸ eqj ▸ he1.refl n
        else
          have hj: j < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) eqj
          have ⟨k, hk, relk⟩ := cond_eq.mp ⟨j, hj, eqi ▸ (he2.symm i j rel)⟩
          eqi ▸ he1.trans n k j
            (he1.symm k n relk)
            (hrec k j hk hj (he2.trans k n j (h k n relk) (eqi ▸ rel)))
      else
        have hi: i < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eqi
        if eqj: j = n then
          have ⟨k, hk, relk⟩ := cond_eq.mp ⟨i, hi, eqj ▸ rel⟩
          eqj ▸ he1.trans i k n
            (hrec i k hi hk (he2.trans i n k (eqj ▸ rel) (he2.symm k n (h k n relk))))
            relk
        else
          have hj: j < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) eqj
          hrec i j hi hj rel


theorem card_rel_congr {r₁ r₂: Nat → Nat → Bool}:
    {n: Nat} → (∀ i j, i < n → j < n → r₁ i j = r₂ i j) → card_rel r₁ n = card_rel r₂ n
  | 0 => fun _ => rfl
  | n + 1 => fun h =>
    have hrec: ∀ i j, i < n → j < n → r₁ i j = r₂ i j :=
      fun i j hi hj => h i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj)
    ite_congr (propext ⟨
      fun ⟨i, hi, ri⟩ => ⟨i, hi, (h i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n)) ▸ ri⟩,
      fun ⟨i, hi, ri⟩ => ⟨i, hi, (h i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n)) ▸ ri⟩
    ⟩)
    (fun _ => card_rel_congr hrec)
    (fun _ => congrArg (· + 1) (card_rel_congr hrec))


def card_fun {α} [DecidableEq α] (f: Nat → α) (n: Nat): Nat := ((List.range n).map f).card


theorem card_fun_rel {α} [d: DecidableEq α] {f: Nat → α} {n: Nat}:
    card_fun f n = card_rel (fun i j => f i = f j) n :=
  match n with
  | 0 => rfl
  | n + 1 =>
    have simpl: card_fun f (n + 1) =
        if f n ∈ (List.range n).map f
        then ((List.range n).map f).card
        else ((List.range n).map f).card + 1 :=
      (@card_fun.eq_def _ d _ _).symm ▸ List.range_succ ▸
      List.map_append ▸ List.map_singleton ▸ List.card_concat
    simpl ▸ ite_congr (propext ⟨
      fun h => have ⟨a, ha, eq⟩ := List.mem_map.mp h
        ⟨a, List.mem_range.mp ha, decide_eq_true eq⟩,
      fun ⟨a, ha, rel⟩ => List.mem_map.mpr
        ⟨a, List.mem_range.mpr ha, of_decide_eq_true rel⟩
    ⟩) (fun _ => card_fun_rel) (fun _ => congrArg (· + 1) card_fun_rel)


theorem rel_fun_rel_imp {n: Nat} {p q: Partition n} (h: ∀ i j, p.rel i j → q.rel i j):
    ∀ i j: Nat, decide (p.part[i]? = p.part[j]?) → decide (q.part[i]? = q.part[j]?) :=
  fun i j rel =>
    have rel := of_decide_eq_true rel
    if hi: i < n then
      have ⟨hj, eq⟩ := Vector.getElem?_eq_some_iff.mp
        (Vector.getElem?_eq_getElem hi ▸ rel).symm
      decide_eq_true ((Vector.getElem?_eq_getElem hi ▸ Vector.getElem?_eq_getElem hj ▸
        congrArg some (h ⟨i, hi⟩ ⟨j, hj⟩ eq.symm)))
    else
      have hi: n ≤ i := Nat.le_of_not_lt hi
      have hj: n ≤ j := Vector.getElem?_eq_none_iff.mp
        (Vector.getElem?_eq_none hi ▸ rel).symm
      decide_eq_true ((Vector.getElem?_eq_none hi) ▸ (Vector.getElem?_eq_none hj) ▸ rfl)


theorem fun_rel_equiv {n: Nat} {p: Partition n}:
    BEquivalence fun i j => decide (p.part[i]? = p.part[j]?) := {
  refl := fun _ => decide_eq_true rfl
  symm := fun _ _ h => decide_eq_true (of_decide_eq_true h).symm
  trans := fun _ _ _ h1 h2 => decide_eq_true ((of_decide_eq_true h1).trans (of_decide_eq_true h2))
}


namespace Partition

theorem card_eq_card_fun {n: Nat} {p: Partition n}:
    p.card = card_fun (fun i => p.part[i]?) n :=
  (List.card_map_inj some
    (fun _ _ => Option.some_inj.mp)).symm.trans
    (Eq.trans (congrArg List.card (
      have length1: (List.map some (Vector.map Fin.val p.part).toList).length = n :=
        ((List.length_map _).trans Vector.length_toList)
      have length2: (List.map (Option.map Fin.val) (List.map (fun i => p.part[i]?) (List.range n))).length = n :=
        (((List.length_map _).trans (List.length_map _)).trans List.length_range)
      List.ext_getElem (length1.trans length2.symm)
        (fun i hi1 hi2 =>
          have left: ((p.part.map Fin.val).toList.map some)[i] = some p.part[i].val :=
            List.getElem_map _ ▸ Vector.getElem_toList _ ▸
              congrArg some (Vector.getElem_map Fin.val (length1 ▸ hi1))
          have right: ((List.map (fun i => p.part[i]?) (List.range n)).map (Option.map Fin.val))[i] =
              Option.map Fin.val (some p.part[i]) :=
            List.getElem_map _ ▸ List.getElem_map _ ▸
            List.getElem_range _ ▸ Vector.getElem?_eq_getElem _ ▸ rfl
          left.trans (rfl.trans right.symm)
        )
      )) (List.card_map_inj (Option.map Fin.val)
    (fun _ _ => (Option.map_inj_right fun _ _ => Fin.val_inj.mp).mp)))


theorem card_eq_card_rel {n: Nat} {p: Partition n}:
    p.card = card_rel (fun i j => p.part[i]? = p.part[j]?) n :=
  card_eq_card_fun.trans card_fun_rel


theorem card_anti {n: Nat} {p q: Partition n} (h: ∀ i j, p.rel i j → q.rel i j):
    q.card ≤ p.card :=
  (card_eq_card_rel (p := q)) ▸
  (card_eq_card_rel (p := p)) ▸
  card_rel_anti (rel_fun_rel_imp h)


theorem card_anti_eq {n: Nat} {p q: Partition n} (h: ∀ i j, p.rel i j → q.rel i j):
    q.card = p.card → q.rel = p.rel := fun eq =>
  have concl := card_rel_anti_eq (rel_fun_rel_imp h) fun_rel_equiv fun_rel_equiv
    ((card_eq_card_rel (p := q)) ▸
    (card_eq_card_rel (p := p)) ▸ eq)
  funext (fun i => funext (fun j => propext (
    ⟨
      (fun rel =>
        have res := concl i.val j.val i.isLt j.isLt (decide_eq_true
          (Vector.getElem?_eq_getElem i.isLt ▸ Vector.getElem?_eq_getElem j.isLt ▸ congrArg some rel))
        Option.some_inj.mp (Vector.getElem?_eq_getElem i.isLt ▸ Vector.getElem?_eq_getElem j.isLt ▸
          of_decide_eq_true res)
      ),
      h i j
    ⟩
  )))


public theorem intersection_card_ge {n: Nat} {s: Nat} {f: Nat → Partition n} {i: Nat} (hi: i < s):
    (f i).card ≤ (intersection s f).card :=
  card_anti (fun _ _ h => intersection_correct.mp h i hi)


public theorem of_intersection_card_eq {n: Nat} {s: Nat} {f: Nat → Partition n} {i: Nat} (hi: i < s):
    (f i).card = (intersection s f).card → (f i).rel = (intersection s f).rel :=
  fun eq => card_anti_eq (fun _ _ h => intersection_correct.mp h i hi) eq

/-
Create a normalized partition from a binary predicate
-/
def predPart {n: Nat} (p: Fin n → Bool): Partition n := {
  k := 2
  part := Vector.ofFn (fun s => if p s then 1 else 0)
}


theorem bool_eq_iff_ite_01_eq {a b: Bool}:
    a = b ↔ (if a then (1: Fin 2) else (0: Fin 2)) = (if b then (1: Fin 2) else (0: Fin 2)) :=
  ⟨
    fun h => h ▸ (Eq.refl (if a = true then 1 else 0)),
    fun h => match a with
      | false => match b with
        | false => rfl
        | true => nomatch h
      | true => match b with
        | false => nomatch h
        | true => rfl
  ⟩


theorem predPart_correct {n: Nat} {p: Fin n → Bool} {i j: Fin n}:
    (predPart p).rel i j ↔ p i = p j :=
  rel.eq_def _ _ _ ▸ Vector.get_ofFn ▸ Vector.get_ofFn ▸
    bool_eq_iff_ite_01_eq.symm


public def predPartNormalized {n: Nat} (p: Fin n → Bool): Partition n :=
  let part := predPart p
  intersection 1 (fun _ => part)


public theorem predPartNormalized_correct {n: Nat} {p: Fin n → Bool} {i j: Fin n}:
    (predPartNormalized p).rel i j ↔ p i = p j :=
  intersection_correct.trans ⟨
    fun h => predPart_correct.mp (h 0 Nat.zero_lt_one),
    fun h => (fun _ _ => predPart_correct.mpr h)
  ⟩


public theorem predPartNormalized_normalized {n: Nat} {p: Fin n → Bool}:
    (predPartNormalized p).normalized :=
  intersection_normalized

end Partition
