/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

import AutoKchp.Internal.Counting
import AutoKchp.Internal.Util

/-
Counting sort table construction
-/

def addToTable {k: Nat} (f: Nat → Fin k) (v: Vector (List Nat) k): Nat → Vector (List Nat) k
  | 0 => v
  | n + 1 => addToTable f (v.modify (f n) (fun l => n::l)) n


theorem addToTable_swap_append {k: Nat} {f: Nat → Fin k} {v: Vector (List Nat) k}
  {i: Fin k} {l: List Nat}:
    {n: Nat} →
    addToTable f (v.modify i (fun u => u ++ l)) n = (addToTable f v n).modify i (fun u => u ++ l)
  | 0 => rfl
  | n + 1 =>
    have hrec := addToTable_swap_append (v := v.modify (f n) fun l => n::l)
    hrec ▸ congrArg (fun w => addToTable f w n) (Vector.modify_comm rfl)


def constructTable {k: Nat} (f: Nat → Fin k): Nat → Vector (List Nat) k :=
  addToTable f (Vector.replicate k [])


--constructTable is difficult to reason about directly, so we introduce the following version
def constructTable' {k: Nat} (f: Nat → Fin k): Nat → Vector (List Nat) k
  | 0 => Vector.replicate k []
  | n + 1 => (constructTable' f n).modify (f n) (fun l => l ++ [n])


theorem constructTable_eq_constructTable' {k: Nat} {f: Nat → Fin k}:
    {n: Nat} → constructTable f n = constructTable' f n
  | 0 => rfl
  | n + 1 =>
    have base_swap:
        ((Vector.replicate k []).modify (f n) fun l => n :: l) =
        ((Vector.replicate k []).modify (f n) fun l => l ++ [n]) := Vector.get_ext (fun i =>
          if eq: f n = i then
            eq ▸
            Vector.get_modify_self.symm ▸
            Vector.get_modify_self.symm ▸
            Vector.get_replicate.symm ▸ rfl
          else
            (Vector.get_modify_of_ne eq).symm ▸
            (Vector.get_modify_of_ne eq).symm ▸ rfl
        )
    have c: addToTable f ((Vector.replicate k []).modify (f n) fun l => n :: l) n =
        (constructTable' f n).modify (f n) fun l => l ++ [n] :=
      constructTable_eq_constructTable' ▸ addToTable_swap_append ▸
      congrArg (fun w => addToTable f w n) base_swap; c


theorem constructTable'_prefix {k: Nat} {f: Nat → Fin k} {i: Fin k} {p q: Nat} (h: p ≤ q):
    (constructTable' f p).get i <+: (constructTable' f q).get i := match q with
  | 0 => (Nat.eq_zero_of_le_zero h) ▸ List.prefix_rfl
  | n + 1 =>
    if eq1: p = n + 1 then
      (congrArg (fun x => (constructTable' f x).get i) eq1) ▸ List.prefix_rfl
    else
      have h := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h eq1)
      if eq2: f n = i then
        eq2 ▸ Vector.get_modify_self ▸
          (List.IsPrefix.trans (constructTable'_prefix h) (List.prefix_append _ [n]))
      else
        (Vector.get_modify_of_ne eq2).symm ▸ (constructTable'_prefix h)


--Surjectivity - main correctness lemma
theorem constructTable'_mem_self {k: Nat} {f: Nat → Fin k} {n: Nat}:
    n ∈ (constructTable' f (n + 1)).get (f n) :=
  Vector.get_modify_self ▸ (List.mem_append_right _ (List.mem_singleton_self n))


theorem constructTable'_mem_of_lt {k: Nat} {f: Nat → Fin k} {p q: Nat} (h: p < q):
    p ∈ (constructTable' f q).get (f p) :=
  have ⟨_, hl⟩ := constructTable'_prefix h
  hl ▸ List.mem_append_left _ (constructTable'_mem_self)


theorem constructTable'_f_eq_of_mem {k: Nat} {f: Nat → Fin k} {i: Fin k} {p: Nat}:
    {n: Nat} → p ∈ (constructTable' f n).get i → f p = i
  | 0 => fun hp => False.elim (List.not_mem_nil (Vector.get_replicate ▸ hp))
  | n + 1 => fun hp => if eq: f n = i then
    match List.mem_append.mp (Vector.get_modify_self ▸ eq ▸ hp) with
      | Or.inl h => constructTable'_f_eq_of_mem (eq ▸ h)
      | Or.inr h => (List.mem_singleton.mp h) ▸ eq
  else
    constructTable'_f_eq_of_mem ((Vector.get_modify_of_ne eq) ▸ hp)


theorem constructTable'_lt {k: Nat} {f: Nat → Fin k} {i: Fin k}:
    {n: Nat} → ∀ p: Nat, p ∈ (constructTable' f n).get i → p < n
  | 0 => fun _ hp => False.elim (List.not_mem_nil (Vector.get_replicate ▸ hp))
  | n + 1 => fun p hp => if eq: f n = i then
      match List.mem_append.mp (Vector.get_modify_self ▸ eq ▸ hp) with
        | Or.inl h => Nat.lt_succ_of_lt (constructTable'_lt p h)
        | Or.inr h => Nat.lt_succ_of_le (Nat.le_of_eq (List.mem_singleton.mp h))
    else
      Nat.lt_succ_of_lt (constructTable'_lt p ((Vector.get_modify_of_ne eq) ▸ hp))


theorem constructTable'_mem_iff {k: Nat} {f: Nat → Fin k} {i: Fin k} {p q: Nat}:
    p ∈ (constructTable' f q).get i ↔ (p < q ∧ f p = i) :=
  ⟨
    fun mem => ⟨constructTable'_lt p mem, constructTable'_f_eq_of_mem mem⟩,
    fun ⟨lt, eq⟩ => eq ▸ constructTable'_mem_of_lt lt
  ⟩


--Injectivity

theorem constructTable'_nodup {k: Nat} {f: Nat → Fin k} {i: Fin k}:
    {n: Nat} → ((constructTable' f n).get i).Nodup
  | 0 => Vector.get_replicate ▸ List.nodup_nil
  | n + 1 =>
    if eq: f n = i then
      eq ▸ Vector.get_modify_self ▸ (List.nodup_append_singleton
        (fun mem => Nat.ne_of_lt (constructTable'_lt n mem) rfl)
        constructTable'_nodup)
    else
      (Vector.get_modify_of_ne eq).symm ▸ constructTable'_nodup


--Stability
theorem contructTable'_stable_self {k: Nat} {f: Nat → Fin k} {p q: Nat}
  (h: f p = f q) (hlt: p < q):
    [p, q].Sublist ((constructTable' f (q + 1)).get (f q)) :=
  have cons_append: [p, q] = [p] ++ [q] := rfl
  Vector.get_modify_self ▸ cons_append ▸ List.Sublist.append
    (List.singleton_sublist.mpr (h ▸ constructTable'_mem_of_lt hlt))
    (List.Sublist.refl _)


theorem constructTable'_stable_of_lt {k: Nat} {f: Nat → Fin k} {p q n: Nat}
  (h: f p = f q) (h1: p < q) (h2: q < n):
    [p, q].Sublist ((constructTable' f n).get (f q)) :=
  have ⟨_, hl⟩ := constructTable'_prefix h2
  hl ▸ List.sublist_append_of_sublist_left (contructTable'_stable_self h h1)


--Same lemmas, but for constructTable

--Every Nat is sorted in the correct bin, and only the correct bin
theorem constructTable_mem_iff {k: Nat} {f: Nat → Fin k} {i: Fin k} {p q: Nat}:
    p ∈ (constructTable f q).get i ↔ (p < q ∧ f p = i) :=
  constructTable_eq_constructTable' ▸ constructTable'_mem_iff

--Every Nat appears at most once per bin
theorem constructTable_nodup {k: Nat} {f: Nat → Fin k} {i: Fin k} {n: Nat}:
    ((constructTable f n).get i).Nodup :=
  constructTable_eq_constructTable' ▸ constructTable'_nodup

--Nats in the same bin keep their order
theorem constructTable_stable_of_lt {k: Nat} {f: Nat → Fin k} {p q n: Nat}
  (h: f p = f q) (h1: p < q) (h2: q < n):
    [p, q].Sublist ((constructTable f n).get (f q)) :=
  constructTable_eq_constructTable' ▸ constructTable'_stable_of_lt h h1 h2


/-
Counting sort
-/

def countingSort {k: Nat} (f: Nat → Fin k) (n: Nat): Array Nat :=
  (constructTable f n).toArray.flattenLists


--Again, we use a simpler version with the builtin List.flatten for proofs
def countingSort' {k: Nat} (f: Nat → Fin k) (n: Nat): Array Nat :=
  (constructTable f n).toList.flatten.toArray


theorem countingSort_eq_countingSort' {k: Nat} {f: Nat → Fin k} {n: Nat}:
    countingSort f n = countingSort' f n :=
  Array.eq_toArray.mpr Array.toList_flattenLists_eq_flatten_toList


--Surjectivity

theorem countingSort'_mem_of_lt {k: Nat} {f: Nat → Fin k} {p q: Nat} (h: p < q):
    p ∈ countingSort' f q :=
  List.mem_toArray.mpr (List.mem_flatten.mpr ⟨
    (constructTable f q).get (f p),
    Vector.mem_toList_iff.mpr Vector.get_mem,
    constructTable_mem_iff.mpr ⟨h, rfl⟩
  ⟩)


theorem countingSort'_lt {k: Nat} {f: Nat → Fin k} {n: Nat}:
    ∀ p: Nat, p ∈ countingSort' f n → p < n :=
  fun _ hp =>
    have ⟨_, hl, hp⟩ := List.mem_flatten.mp (List.mem_toArray.mp hp)
    have ⟨_, hi⟩ := Vector.exists_get_of_mem (Vector.mem_toList_iff.mp hl)
    (constructTable_mem_iff.mp (hi ▸ hp)).left


theorem countingSort'_mem_iff {k: Nat} {f: Nat → Fin k} {n: Nat}:
    ∀ p: Nat, p ∈ countingSort' f n ↔ p < n :=
  fun p => ⟨countingSort'_lt p, countingSort'_mem_of_lt⟩


--Injectivity
theorem constructTable_pairwise_disjoint {k: Nat} {f: Nat → Fin k} {n: Nat}:
    (constructTable f n).toList.Pairwise List.Disjoint :=
  List.pairwise_iff_getElem.mpr (fun i j hi hj lt a ha_i ha_j =>
    have length_constructTable: (constructTable f n).toList.length = k := Vector.length_toList
    let i_fin: Fin k := ⟨i, length_constructTable ▸ hi⟩
    let j_fin: Fin k := ⟨j, length_constructTable ▸ hj⟩
    have ha_i_fin: a ∈ (constructTable f n).get i_fin := Vector.getElem_toList' ▸ ha_i
    have ha_j_fin: a ∈ (constructTable f n).get j_fin := Vector.getElem_toList' ▸ ha_j
    have f_i_fin: f a = i_fin := (constructTable_mem_iff.mp ha_i_fin).right
    have f_j_fin: f a = j_fin := (constructTable_mem_iff.mp ha_j_fin).right
    have eq: i = j := Fin.val_congr (Eq.trans f_i_fin.symm f_j_fin)
    Nat.ne_of_lt lt eq
  )


theorem countingSort'_nodup {k: Nat} {f: Nat → Fin k} {n: Nat}:
    (countingSort' f n).toList.Nodup :=
  List.toList_toArray ▸ List.nodup_flatten constructTable_pairwise_disjoint (fun _ hu =>
    have ⟨_, hi⟩ := Vector.get_of_mem (Vector.mem_toList_iff.mp hu)
    hi ▸ constructTable_nodup
  )


--Sorting correctness
theorem countingSort'_order {k: Nat} {f: Nat → Fin k} {p q n: Nat}
  (h: f p < f q) (h1: p < n) (h2: q < n):
    [p, q].Sublist (countingSort' f n).toList :=
  List.toList_toArray ▸ (
    List.pair_sublist_flatten ⟨
      (constructTable f n).get (f p),
      (constructTable f n).get (f q),
      constructTable_mem_iff.mpr ⟨h1, rfl⟩,
      constructTable_mem_iff.mpr ⟨h2, rfl⟩,
      Vector.pair_get_sublist_toList h,
    ⟩
  )


--Stability
theorem countingSort'_stable {k: Nat} {f: Nat → Fin k} {p q n: Nat}
  (h: f p = f q) (h1: p < q) (h2: q < n):
    [p, q].Sublist (countingSort' f n).toList :=
  List.toList_toArray ▸ List.sublist_flatten_of_sublist_elem
    ⟨
      (constructTable f n).get (f q),
      Vector.mem_toList_iff.mpr Vector.get_mem,
      constructTable_stable_of_lt h h1 h2
    ⟩


--Same lemmas, but for countingSort

--Every Nat appears in the Array
theorem countingSort_mem_iff {k: Nat} {f: Nat → Fin k} {n: Nat}:
    ∀ p: Nat, p ∈ countingSort f n ↔ p < n :=
  countingSort_eq_countingSort' ▸ countingSort'_mem_iff

--Every Nat appear at most once in the Array
theorem countingSort_nodup {k: Nat} {f: Nat → Fin k} {n: Nat}:
    (countingSort f n).toList.Nodup :=
  countingSort_eq_countingSort' ▸ countingSort'_nodup

--countingSort sorts
theorem countingSort_order {k: Nat} {f: Nat → Fin k} {p q n: Nat}
  (h: f p < f q) (h1: p < n) (h2: q < n):
    [p, q].Sublist (countingSort f n).toList :=
  countingSort_eq_countingSort' ▸ (countingSort'_order h h1 h2)

--countingSort is stable
theorem countingSort_stable {k: Nat} {f: Nat → Fin k} {p q n: Nat}
  (h: f p = f q) (h1: p < q) (h2: q < n):
    [p, q].Sublist (countingSort f n).toList :=
  countingSort_eq_countingSort' ▸ (countingSort'_stable h h1 h2)


/-
Radix sort from a given permutation
-/
def radixSortFrom {radix: Nat → Nat} (f: Nat → (r: Nat) → Fin (radix r)) (v: Array Nat):
    (s: Nat) → Array Nat
  | 0 => v
  | s + 1 => radixSortFrom f (v.compose (countingSort (fun p => f (v.getD p 0) s) v.size)) s


--Surjectivity
theorem countingSort_size {k: Nat} {f: Nat → Fin k} {n: Nat}:
    (countingSort f n).size = n :=
  Array.length_toList ▸ List.perm_length_eq (fun i => ⟨
    fun hi => Array.mem_toList_iff.mpr ((countingSort_mem_iff i).mpr hi),
    fun hi => ((countingSort_mem_iff i).mp (Array.mem_toList_iff.mp hi)),
  ⟩) countingSort_nodup


theorem radixSortFrom_mem_iff {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)}
  {v: Array Nat} (h: ∀ p: Nat, p < v.size ↔ p ∈ v):
    {s: Nat} → ∀ p: Nat, p < v.size ↔ p ∈ radixSortFrom f v s
  | 0 => h
  | s + 1 => fun p =>
    have size_eq: (v.compose (countingSort (fun z => f (v.getD z 0) s) v.size)).size = v.size :=
      Array.size_compose.symm ▸ countingSort_size
    size_eq ▸ radixSortFrom_mem_iff (fun q =>
      ⟨
        fun hq => have ⟨iq, hiq, eq⟩ := Array.getElem_of_mem ((h q).mp (size_eq ▸ hq))
          Array.mem_map.mpr ⟨iq,
            (countingSort_mem_iff iq).mpr hiq,
            eq ▸ (Array.getElem_eq_getD 0).symm
          ⟩,
        fun hq => have ⟨iq, hiq, eq⟩ := Array.mem_map.mp hq
          size_eq.symm ▸ (h q).mpr
            (eq ▸ (Array.getElem_eq_getD (h := (countingSort_mem_iff iq).mp hiq) 0) ▸
            Array.getElem_mem _)
      ⟩
    ) p

--Injectivity
theorem radixSortFrom_nodup {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)}
  {v: Array Nat} (h: v.toList.Nodup):
    {s: Nat} → (radixSortFrom f v s).toList.Nodup
  | 0 => h
  | _ + 1 => radixSortFrom_nodup (Array.compose_nodup h countingSort_nodup
      (fun p hp => (countingSort_mem_iff p).mp hp))


--Sorting correctness
@[expose]
public def lexEq {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)) (r: Nat): Prop :=
  ∀ i: Nat, i < r → f i = g i


@[expose]
public def lexLt {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)):
    Nat → Prop
  | 0 => False
  | r + 1 => (lexLt f g r) ∨ ((lexEq f g r) ∧ (f r < g r))


theorem radixSortFrom_stable {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {v: Array Nat}
  {p q s: Nat} (h1: lexEq (f p) (f q) s) (h2: [p, q].Sublist v.toList):
    [p, q].Sublist (radixSortFrom f v s).toList :=
  match s with
  | 0 => h2
  | s + 1 =>
    have ⟨ip, iq, hip, hiq, eqp, eqq⟩ := List.exists_pair_getElem_of_sublist h2
    have hiq: iq < v.size := Array.length_toList ▸ hiq
    have eqp: v[ip] = p := eqp; have eqq: v[iq] = q := eqq
    have vip: v.getD ip 0 = p := Array.getElem_eq_getD 0 ▸ eqp
    have viq: v.getD iq 0 = q := Array.getElem_eq_getD 0 ▸ eqq
    have f_eq: f (v.getD ip 0) s = f (v.getD iq 0) s := viq ▸ vip ▸ h1 s (Nat.lt_succ_self _)
    radixSortFrom_stable (s := s) (fun i hi => h1 i (Nat.lt_succ_of_lt hi))
      (eqp ▸ eqq ▸ Array.compose_sublist_pair
        (countingSort_stable f_eq hip hiq) (Nat.lt_trans hip hiq) hiq)


theorem radixSortFrom_order {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {v: Array Nat}
  {p q s: Nat} (h: lexLt (f p) (f q) s) (h1: p ∈ v) (h2: q ∈ v):
    [p, q].Sublist (radixSortFrom f v s).toList :=
  match s with
  | 0 => False.elim h
  | s + 1 => match h with
    | .inl tail_lt => radixSortFrom_order (s :=s) tail_lt
        (Array.mem_compose_of_mem h1 (fun i => (countingSort_mem_iff i).mpr))
        (Array.mem_compose_of_mem h2 (fun i => (countingSort_mem_iff i).mpr))
    | .inr ⟨tail_eq, lt⟩ =>
      have ⟨ip, hip, eqp⟩ := Array.getElem_of_mem h1
      have ⟨iq, hiq, eqq⟩ := Array.getElem_of_mem h2
      have fvip: f (v.getD ip 0) s = f p s := (Array.getElem_eq_getD 0 ▸ eqp) ▸ rfl
      have fviq: f (v.getD iq 0) s = f q s := (Array.getElem_eq_getD 0 ▸ eqq) ▸ rfl
      radixSortFrom_stable (s := s) tail_eq (eqp ▸ eqq ▸ Array.compose_sublist_pair
        (countingSort_order (fvip ▸ fviq ▸ lt) hip hiq) hip hiq)


/-
Radix sort
-/

public def radixSort {radix: Nat → Nat} (f: Nat → (r: Nat) → Fin (radix r)) (n: Nat): Nat → Array Nat :=
  radixSortFrom f (Array.range n)


public theorem radixSort_mem_iff {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}:
    ∀ p: Nat, p < n ↔ p ∈ radixSort f n s :=
  have concl: ∀ p: Nat, p < (Array.range n).size ↔ p ∈ radixSort f n s :=
    radixSortFrom_mem_iff  (fun _ => Array.size_range ▸ Array.mem_range.symm)
  fun p => ⟨
    fun hp => (concl p).mp (Array.size_range ▸ hp),
    fun hp => Nat.lt_of_lt_of_eq ((concl p).mpr hp) Array.size_range
  ⟩


public theorem radixSort_nodup {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}:
    (radixSort f n s).toList.Nodup :=
  radixSortFrom_nodup (Array.toList_range ▸ List.nodup_range)


public theorem radixSort_order {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n: Nat}
  {p q s: Nat} (h: lexLt (f p) (f q) s) (h1: p < n) (h2: q < n):
    [p, q].Sublist (radixSort f n s).toList :=
  radixSortFrom_order h (Array.mem_range.mpr h1) (Array.mem_range.mpr h2)

--More traditional formulation of correctness, easier to use
@[expose]
public def lexLe {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)) (n: Nat): Prop :=
  lexLt f g n ∨ lexEq f g n


public theorem lexLe_or_lexLt {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)):
     (n: Nat) → lexLe f g n ∨ lexLt g f n
  | 0 => Or.inl (Or.inr (fun i hi => False.elim (Nat.not_lt_zero i hi)))
  | n + 1 => match lexLe_or_lexLt f g n with
    | .inl (.inl lt) => Or.inl (Or.inl (Or.inl lt))
    | .inl (.inr eq) => match Nat.lt_trichotomy (f n) (g n) with
      | .inl lt => Or.inl (Or.inl (Or.inr ⟨eq, lt⟩))
      | .inr (.inl eq2) => Or.inl (Or.inr (fun i hi =>
        match Nat.lt_succ_iff_lt_or_eq.mp hi with
        | .inl hi => eq i hi
        | .inr hi => Fin.eq_of_val_eq (hi ▸ eq2)
      ))
      | .inr (.inr lt) => Or.inr (Or.inr ⟨(fun i hi => (eq i hi).symm), lt⟩)
    | .inr lt => Or.inr (Or.inl lt)


public theorem radixSort_size {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}:
   (radixSort f n s).size = n :=
  List.perm_length_eq (fun p => ⟨
    fun hp => Array.mem_toList_iff.mpr ((radixSort_mem_iff p).mp hp),
    fun hp => (radixSort_mem_iff p).mpr (Array.mem_toList_iff.mp hp)
  ⟩) radixSort_nodup


public theorem radixSort_order' {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n: Nat}
  {i j s: Nat} (hi: i < n) (hj: j < n) (h: i ≤ j):
    lexLe
      (f ((radixSort f n s)[i]'(radixSort_size ▸ hi)))
      (f ((radixSort f n s)[j]'(radixSort_size ▸ hj))) s :=
  if eq: i = j then
    Or.inr (fun k hj => eq ▸ rfl)
  else
    let p := (radixSort f n s)[i]'(radixSort_size ▸ hi)
    let q := (radixSort f n s)[j]'(radixSort_size ▸ hj)
    have p_lt: p < n := (radixSort_mem_iff p).mpr (Array.getElem_mem _)
    have q_lt: q < n := (radixSort_mem_iff q).mpr (Array.getElem_mem _)
    match lexLe_or_lexLt (f p) (f q) s with
    | .inl le => le
    | .inr lt =>
      have sublist: [q, p].Sublist (radixSort f n s).toList :=
        radixSort_order lt q_lt p_lt
      have ineq1: i < j := Nat.lt_of_le_of_ne h eq
      have ⟨i2, j2, hi2, hj2, eqp, eqq⟩ := List.exists_pair_getElem_of_sublist sublist
      have nodup: (radixSort f n s).toList.Nodup := radixSort_nodup
      have i2_eq_j: i2 = j := List.idx_inj_of_nodup nodup _ _ eqp
      have j2_eq_i: j2 = i := List.idx_inj_of_nodup nodup _ _ eqq
      have ineq2: j < i := i2_eq_j ▸ j2_eq_i ▸ hi2
      False.elim (Nat.not_lt_of_gt ineq1 ineq2)
