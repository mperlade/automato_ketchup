import Automata.Counting

/-
Counting sort table construction
-/

def Vector.modify {α} {k: Nat} (v: Vector α k) (i: Fin k) (f: α → α): Vector α k :=
  ⟨v.toArray.modify i.val f, Eq.trans Array.size_modify v.size_toArray⟩


theorem Vector.get_modify_self {α} {k: Nat} {v: Vector α k} {i: Fin k} {f: α → α}:
    (v.modify i f).get i = f (v.get i) :=
  Array.getElem_modify_self f ((v.modify i f).size_toArray.symm ▸ i.isLt)


theorem Vector.get_modify_of_ne {α} {k: Nat} {v: Vector α k} {i j: Fin k} {f: α → α} (h: i ≠ j):
    (v.modify i f).get j = v.get j :=
  Array.getElem_modify_of_ne (Fin.val_ne_iff.mpr h) f ((v.modify i f).size_toArray.symm ▸ j.isLt)


theorem Vector.get_ext {α} {k: Nat} {v w: Vector α k} (h: ∀ i: Fin k, v.get i = w.get i): v = w :=
  Vector.ext (fun i hi => h ⟨i, hi⟩)


theorem Vector.get_replicate {α} {k: Nat} {a: α} {i: Fin k}: (Vector.replicate k a).get i = a :=
  have lt: i.val < (Vector.replicate k a).toArray.size :=
    ((Vector.replicate k a).size_toArray.symm) ▸ i.isLt
  Array.getElem_replicate lt


theorem Vector.modify_modify_self {α} {k: Nat} {v: Vector α k} {i: Fin k} {f g: α → α}:
    (v.modify i f).modify i g = v.modify i (g ∘ f) :=
  Vector.get_ext (fun j =>
    if eq: i = j then
        eq.symm ▸
        Vector.get_modify_self.symm ▸
        Vector.get_modify_self.symm ▸
        Vector.get_modify_self.symm ▸ rfl
    else
        (Vector.get_modify_of_ne eq).symm ▸
        (Vector.get_modify_of_ne eq).symm ▸
        (Vector.get_modify_of_ne eq).symm ▸ rfl
  )


theorem Vector.modify_modify_of_ne {α} {k: Nat} {v: Vector α k} {i j: Fin k} {f g: α → α} (h: i ≠ j):
    (v.modify i f).modify j g = (v.modify j g).modify i f :=
  Vector.get_ext (fun a =>
    if eqi: i = a then
      eqi ▸
      (Vector.get_modify_of_ne h.symm).symm ▸
      Vector.get_modify_self.symm ▸
      Vector.get_modify_self.symm ▸
      (Vector.get_modify_of_ne h.symm).symm ▸ rfl
    else if eqj: j = a then
      eqj ▸
      (Vector.get_modify_of_ne h).symm ▸
      Vector.get_modify_self.symm ▸
      Vector.get_modify_self.symm ▸
      (Vector.get_modify_of_ne h).symm ▸ rfl
    else
      (Vector.get_modify_of_ne eqi).symm ▸
      (Vector.get_modify_of_ne eqj).symm ▸
      (Vector.get_modify_of_ne eqj).symm ▸
      (Vector.get_modify_of_ne eqi).symm ▸ rfl
  )


theorem Vector.modify_comm {α} {k: Nat} {v: Vector α k} {i j: Fin k}
  {f: α → α} {g: α → α} (h: g ∘ f = f ∘ g):
    (v.modify i f).modify j g = (v.modify j g).modify i f :=
  if eq: i = j then
    eq ▸
    Vector.modify_modify_self.symm ▸
    Vector.modify_modify_self.symm ▸
    (congrArg _ h)
  else
    Vector.modify_modify_of_ne eq


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
theorem List.nodup_singleton {α} {a: α}: [a].Nodup :=
  List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩


theorem List.nodup_append_singleton {α} {l: List α} {a: α} (h1: a ∉ l) (h2: l.Nodup):
    (l ++ [a]).Nodup :=
  List.nodup_append.mpr ⟨h2, List.nodup_singleton,
    fun _ hx _ hy hxy => h1 ((hxy ▸ (List.mem_singleton.mp hy)) ▸ hx)⟩


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

theorem List.flatten_append_eq_foldl_append {α} {u: List α}:
    {l: List (List α)} → u ++ l.flatten = l.foldl (fun acc v => acc ++ v) u
  | [] => List.flatten_nil ▸ List.append_nil _ ▸ List.foldl_nil ▸ rfl
  | _::_ => List.flatten_cons.symm ▸ (List.append_assoc _ _ _ ▸ List.flatten_append_eq_foldl_append)


theorem List.flatten_eq_foldl_append {α} {l: List (List α)}:
    l.flatten = l.foldl (fun acc u => acc ++ u) [] :=
  List.flatten_append_eq_foldl_append ▸ List.nil_append _


theorem List.concat_eq_foldl {α} {u: List α}:
    {v: List α} → u ++ v = v.foldl (fun acc a => acc ++ [a]) u
  | [] => (List.append_nil _).symm ▸ (List.foldl_nil ▸ rfl)
  | _::_ => List.foldl_cons.symm ▸ List.concat_eq_foldl ▸ (List.append_cons u _ _) ▸ rfl


theorem List.flatten_eq_foldl_foldl {α} {l: List (List α)}:
    l.flatten = l.foldl (fun acc u => u.foldl (fun acc a => acc ++ [a]) acc) [] :=
  List.flatten_eq_foldl_append ▸ congrArg
    (fun x => l.foldl x [])
    (funext (fun _ => funext (fun _ => List.concat_eq_foldl)))


def Array.flattenLists {α} {v: Array (List α)}: Array α :=
  v.foldl (fun acc l => l.foldl (fun acc a => acc.push a) acc) Array.empty


theorem Array.toList_flattenLists {α} {v: Array (List α)}:
    v.flattenLists.toList = v.foldl (fun acc l => l.foldl (fun acc a => acc ++ [a]) acc) [] :=
  (Array.foldl_hom Array.toList fun _ _ => (
    List.foldl_hom Array.toList fun _ _ => Eq.symm toList_push
  )).symm


theorem Array.toList_flattenLists_eq_flatten_toList {α} {v: Array (List α)}:
    v.flattenLists.toList = v.toList.flatten :=
  Eq.trans ((Array.foldl_toList _) ▸ Array.toList_flattenLists) List.flatten_eq_foldl_foldl.symm


def countingSort {k: Nat} (f: Nat → Fin k) (n: Nat): Array Nat :=
  (constructTable f n).toArray.flattenLists


--Again, we use a simpler version with the builtin List.flatten for proofs
def countingSort' {k: Nat} (f: Nat → Fin k) (n: Nat): Array Nat :=
  (constructTable f n).toList.flatten.toArray


theorem countingSort_eq_countingSort' {k: Nat} {f: Nat → Fin k} {n: Nat}:
    countingSort f n = countingSort' f n :=
  Array.eq_toArray.mpr Array.toList_flattenLists_eq_flatten_toList


--Surjectivity
theorem Vector.get_mem {α} {k: Nat} {v: Vector α k} {i: Fin k}: v.get i ∈ v :=
    Vector.getElem_mem i.isLt


theorem countingSort'_mem_of_lt {k: Nat} {f: Nat → Fin k} {p q: Nat} (h: p < q):
    p ∈ countingSort' f q :=
  List.mem_toArray.mpr (List.mem_flatten.mpr ⟨
    (constructTable f q).get (f p),
    Vector.mem_toList_iff.mpr Vector.get_mem,
    constructTable_mem_iff.mpr ⟨h, rfl⟩
  ⟩)


theorem Vector.exists_get_of_mem {α} {k: Nat} {v: Vector α k} {a: α} (h: a ∈ v):
    ∃ i: Fin k, a = v.get i :=
  have ⟨i, hi, hvi⟩ := Vector.mem_iff_getElem.mp h; ⟨⟨i, hi⟩, hvi.symm⟩


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
def List.Disjoint {α} (u v: List α): Prop := ∀ a: α, a ∈ u → a ∈ v → False


theorem List.nodup_flatten {α} {l: List (List α)}
  (h1: l.Pairwise List.Disjoint) (h2: ∀ u: List α, u ∈ l → u.Nodup):
    l.flatten.Nodup :=
  match l with
  | [] => List.nodup_nil
  | h::_ =>
    List.flatten_cons ▸ List.nodup_append.mpr ⟨
      h2 h List.mem_cons_self,
      List.nodup_flatten (List.pairwise_cons.mp h1).right
        (fun u hu => h2 u (List.mem_cons_of_mem h hu)),
      fun a ha _ hb eq =>
        have ⟨u, hu, hb⟩ := List.mem_flatten.mp hb
        have h_u_disjoint := (List.pairwise_cons.mp h1).left u hu
        h_u_disjoint a ha (eq ▸ hb)
    ⟩


theorem Vector.getElem_toList' {α} {k: Nat} {v: Vector α k} {i: Fin k}:
    v.toList[i] = v.get i := Vector.getElem_toList (Vector.length_toList ▸ i.isLt)


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


theorem Vector.get_of_mem {α} {k: Nat} {v: Vector α k} {a: α} (h: a ∈ v):
    ∃ i: Fin k, v.get i = a :=
  have ⟨i, hi, eq⟩ := Vector.getElem_of_mem h
  ⟨⟨i, hi⟩, eq⟩


theorem countingSort'_nodup {k: Nat} {f: Nat → Fin k} {n: Nat}:
    (countingSort' f n).toList.Nodup :=
  List.toList_toArray ▸ List.nodup_flatten constructTable_pairwise_disjoint (fun _ hu =>
    have ⟨_, hi⟩ := Vector.get_of_mem (Vector.mem_toList_iff.mp hu)
    hi ▸ constructTable_nodup
  )


--Sorting correctness
theorem List.sublist_flatten_of_sublist {α} {u v: List (List α)}:
    u.Sublist v → u.flatten.Sublist v.flatten
  | List.Sublist.slnil => List.Sublist.refl []
  | List.Sublist.cons (l₂ := t) l h => List.Sublist.trans
    (List.sublist_flatten_of_sublist h)
    (List.flatten_cons ▸ (List.sublist_append_right l t.flatten))
  | List.Sublist.cons₂ l h => (List.append_sublist_append_left l).mpr
    (List.sublist_flatten_of_sublist h)


theorem List.pair_sublist_flatten {α} {a b: α} {l: List (List α)}
  (h: ∃ u v: List α, a ∈ u ∧ b ∈ v ∧ [u, v].Sublist l):
    [a, b].Sublist l.flatten :=
  have ⟨u, v, ha, hb, sub⟩ := h
  have s₁: [a, b].Sublist (u ++ v) := (List.singleton_sublist.mpr ha).append
    (List.singleton_sublist.mpr hb)
  have s₂: [u, v].flatten.Sublist l.flatten := List.sublist_flatten_of_sublist sub
  have flatten_append: [u, v].flatten = u ++ v := List.flatten_cons.symm ▸ List.flatten_cons.symm ▸
    List.flatten_nil.symm ▸ (List.append_nil _).symm ▸ rfl
  s₁.trans (flatten_append ▸ s₂)


theorem List.pair_getElem_sublist {α} {l: List α} {i j: Nat}
  (hi: i < l.length) (hj: j < l.length) (h: i < j):
    [l[i], l[j]].Sublist l :=
  have ⟨a, t, hl⟩ := List.exists_cons_of_length_pos (Nat.zero_lt_of_lt hi)
  have length_l: l.length = t.length + 1 := hl ▸ List.length_cons
  have ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt h)
  match i with
  | 0 =>
    have htail: [t[v]].Sublist t := List.singleton_sublist.mpr (List.getElem_mem _)
    have htail': [l[j]].Sublist t := hv ▸ hl ▸ htail
    have a_eq: a = l[0] := hl ▸ rfl
    have c: [l[0], l[j]].Sublist (a::t) := a_eq ▸ (List.Sublist.cons₂ a htail'); hl ▸ c
  | u + 1 =>
    have u_lt: u < t.length := Nat.lt_of_add_lt_add_right (length_l ▸ hi)
    have v_lt: v < t.length := Nat.lt_of_add_lt_add_right (length_l ▸ hv ▸ hj)
    have hrec := List.pair_getElem_sublist u_lt v_lt (Nat.lt_of_add_lt_add_right (hv ▸ h))
    hl ▸ (List.Sublist.cons a (hv ▸ hrec))


theorem Vector.pair_get_sublist_toList {α} {k: Nat} {v: Vector α k} {i j: Fin k} (h: ↑i < ↑j):
    [v.get i, v.get j].Sublist v.toList :=
  Vector.getElem_toList' ▸ Vector.getElem_toList' ▸ (List.pair_getElem_sublist _ _ h)


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
theorem List.sublist_flatten_of_sublist_elem {α} {l: List (List α)} {u: List α}
  (h: ∃ v: List α, v ∈ l ∧ u.Sublist v):
    u.Sublist l.flatten :=
  have ⟨_, hv, hu⟩ := h; hu.trans (List.sublist_flatten_of_mem hv)


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
def Array.compose (v w: Array Nat) :=
  w.map (fun i => v.getD i 0)


theorem Array.getElem_compose {v w: Array Nat} {i: Nat} (hi: i < w.size) (hwi: w[i] < v.size):
    (v.compose w)[i]'(Array.size_map.symm ▸ hi) = v[w[i]] :=
  (Array.getElem_map _ _) ▸ (Array.getElem_eq_getD 0).symm


theorem Array.size_compose {v w: Array Nat}: (v.compose w).size = w.size :=
  Array.size_map


def radixSortFrom {radix: Nat → Nat} (f: Nat → (r: Nat) → Fin (radix r)) (v: Array Nat):
    (s: Nat) → Array Nat
  | 0 => v
  | s + 1 => radixSortFrom f (v.compose (countingSort (fun p => f (v.getD p 0) s) v.size)) s


--Surjectivity
theorem countingSort_size {k: Nat} {f: Nat → Fin k} {n: Nat}:
    (countingSort f n).size = n :=
  Array.length_toList ▸ perm_length_eq (fun i => ⟨
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
theorem Array.compose_nodup {v w: Array Nat} (h1: v.toList.Nodup) (h2: w.toList.Nodup)
  (h3: ∀ i: Nat, i ∈ w → i < v.size):
    (v.compose w).toList.Nodup :=
  List.pairwise_iff_getElem.mpr (fun i j hi hj hij eq =>
    have hi: i < w.size := Array.size_map ▸ Array.length_toList ▸ hi
    have hj: j < w.size := Array.size_map ▸ Array.length_toList ▸ hj
    have hwi: w[i] < v.size := h3 w[i] (Array.getElem_mem hi)
    have hwj: w[j] < v.size := h3 w[j] (Array.getElem_mem hj)
    have eqi: (v.compose w).toList[i] = v[w[i]] := Array.getElem_compose hi hwi
    have eqj: (v.compose w).toList[j] = v[w[j]] := Array.getElem_compose hj hwj
    have eq: v[w[i]] = v[w[j]] := eqi ▸ eqj ▸ eq
    match Nat.lt_trichotomy w[i] w[j] with
    | .inl ineq => List.pairwise_iff_getElem.mp h1 w[i] w[j] hwi hwj ineq eq
    | .inr (.inl eq) => List.pairwise_iff_getElem.mp h2 i j hi hj hij eq
    | .inr (.inr ineq) => List.pairwise_iff_getElem.mp h1 w[j] w[i] hwj hwi ineq eq.symm
  )


theorem radixSortFrom_nodup {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)}
  {v: Array Nat} (h: v.toList.Nodup):
    {s: Nat} → (radixSortFrom f v s).toList.Nodup
  | 0 => h
  | _ + 1 => radixSortFrom_nodup (Array.compose_nodup h countingSort_nodup
      (fun p hp => (countingSort_mem_iff p).mp hp))


--Sorting correctness
def lexEq {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)) (r: Nat): Prop :=
  ∀ i: Nat, i < r → f i = g i


def lexLt {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)):
    Nat → Prop
  | 0 => False
  | r + 1 => (lexLt f g r) ∨ ((lexEq f g r) ∧ (f r < g r))


theorem List.exists_pair_getElem_of_sublist {α} {l: List α} {a b: α} (h: [a, b].Sublist l):
    ∃ ia ib: Nat, ∃ hia: ia < ib, ∃ hib: ib < l.length, l[ia] = a ∧ l[ib] = b :=
  have ⟨ra, rb, hr, amem, sub⟩ := List.cons_sublist_iff.mp h
  have bmem := List.singleton_sublist.mp sub
  have ⟨ria, hria, eqa⟩ := List.getElem_of_mem amem
  have ⟨rib, hrib, eqb⟩ := List.getElem_of_mem bmem
  ⟨
    ria, rib + ra.length,
    Nat.lt_add_left _ hria,
    hr.symm ▸ List.length_append ▸ Nat.add_comm _ _ ▸ Nat.add_lt_add_left hrib _,
    hr.symm ▸ eqa ▸ List.getElem_append_left hria,
    hr.symm ▸ eqb ▸ (List.getElem_append_right' ra hrib).symm
  ⟩


theorem Array.compose_sublist_pair {v w: Array Nat} {a b: Nat} (h1: [a, b].Sublist w.toList)
  (h2: a < v.size) (h3: b < v.size):
    [v[a], v[b]].Sublist (v.compose w).toList :=
  have ⟨ia, ib, hia, hib, eqa, eqb⟩ := List.exists_pair_getElem_of_sublist h1
  have hib: ib < w.size := Array.length_toList ▸ hib
  have eqa: w[ia] = a := eqa; have eqb: w[ib] = b := eqb
  have size_eq: (v.compose w).toList.length = w.toList.length :=
    Array.length_toList ▸ Array.length_toList ▸ Array.size_compose
  have hia': ia < (v.compose w).toList.length := size_eq ▸ Nat.lt_trans hia hib
  have hib': ib < (v.compose w).toList.length := size_eq ▸ hib
  have veqa: v[w[ia]] = v[a] := getElem_congr_idx eqa
  have veqb: v[w[ib]] = v[b] := getElem_congr_idx eqb
  have eqa': (v.compose w).toList[ia] = v[a] :=
    veqa ▸ Array.getElem_toList _ ▸ (Array.getElem_compose (Nat.lt_trans hia hib) (eqa ▸ h2))
  have eqb': (v.compose w).toList[ib] = v[b] :=
    veqb ▸ Array.getElem_toList _ ▸ (Array.getElem_compose hib (eqb ▸ h3))
  eqa' ▸ eqb' ▸ List.pair_getElem_sublist hia' hib' hia


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


theorem Array.mem_compose_of_mem {v w: Array Nat} {n: Nat} (h1: n ∈ v)
  (h2: ∀ i: Nat, i < v.size → i ∈ w): n ∈ v.compose w :=
  have ⟨i, hi, eq⟩ := Array.getElem_of_mem h1
  Array.mem_map.mpr ⟨i, h2 i hi, Array.getElem_eq_getD 0 ▸ eq⟩


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

def radixSort {radix: Nat → Nat} (f: Nat → (r: Nat) → Fin (radix r)) (n: Nat): Nat → Array Nat :=
  radixSortFrom f (Array.range n)


theorem radixSort_mem_iff {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}:
    ∀ p: Nat, p < n ↔ p ∈ radixSort f n s :=
  have concl: ∀ p: Nat, p < (Array.range n).size ↔ p ∈ radixSort f n s :=
    radixSortFrom_mem_iff  (fun _ => Array.size_range ▸ Array.mem_range.symm)
  fun p => ⟨
    fun hp => (concl p).mp (Array.size_range ▸ hp),
    fun hp => Nat.lt_of_lt_of_eq ((concl p).mpr hp) Array.size_range
  ⟩


theorem radixSort_nodup {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}:
    (radixSort f n s).toList.Nodup :=
  radixSortFrom_nodup (Array.toList_range ▸ List.nodup_range)


theorem radixSort_order {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n: Nat}
  {p q s: Nat} (h: lexLt (f p) (f q) s) (h1: p < n) (h2: q < n):
    [p, q].Sublist (radixSort f n s).toList :=
  radixSortFrom_order h (Array.mem_range.mpr h1) (Array.mem_range.mpr h2)

--More traditional formulation of correctness, easier to use
def lexLe {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)) (n: Nat): Prop :=
  lexLt f g n ∨ lexEq f g n


theorem lexLe_or_lexLt {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)):
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


theorem radixSort_size {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}:
   (radixSort f n s).size = n :=
  perm_length_eq (fun p => ⟨
    fun hp => Array.mem_toList_iff.mpr ((radixSort_mem_iff p).mp hp),
    fun hp => (radixSort_mem_iff p).mpr (Array.mem_toList_iff.mp hp)
  ⟩) radixSort_nodup


theorem List.idx_inj_of_nodup {α} {l: List α} (h1: l.Nodup) {i j: Nat} (hi: i < l.length) (hj: j < l.length)
    (h2: l[i] = l[j]): i = j :=
  match Nat.lt_trichotomy i j with
  | .inl lt => False.elim (List.pairwise_iff_getElem.mp h1 i j hi hj lt h2)
  | .inr (.inl eq) => eq
  | .inr (.inr lt) => False.elim (List.pairwise_iff_getElem.mp h1 j i hj hi lt h2.symm)


theorem radixSort_order' {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n: Nat}
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
