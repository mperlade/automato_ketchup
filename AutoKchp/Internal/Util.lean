/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

@[expose]
public section
namespace List

variable {α}

def Disjoint (u v: List α): Prop := ∀ a: α, a ∈ u → a ∈ v → False


theorem nodup_singleton {a: α}: [a].Nodup :=
  nodup_cons.mpr ⟨not_mem_nil, nodup_nil⟩


theorem nodup_append_singleton {l: List α} {a: α} (h1: a ∉ l) (h2: l.Nodup):
    (l ++ [a]).Nodup :=
  nodup_append.mpr ⟨h2, nodup_singleton,
    fun _ hx _ hy hxy => h1 ((hxy ▸ (mem_singleton.mp hy)) ▸ hx)⟩


theorem flatten_append_eq_foldl_append {u: List α}:
    {l: List (List α)} → u ++ l.flatten = l.foldl (fun acc v => acc ++ v) u
  | [] => flatten_nil ▸ append_nil _ ▸ foldl_nil ▸ rfl
  | _::_ => flatten_cons.symm ▸ (append_assoc _ _ _ ▸ flatten_append_eq_foldl_append)


theorem flatten_eq_foldl_append {l: List (List α)}:
    l.flatten = l.foldl (fun acc u => acc ++ u) [] :=
  flatten_append_eq_foldl_append ▸ nil_append _


theorem concat_eq_foldl {u: List α}:
    {v: List α} → u ++ v = v.foldl (fun acc a => acc ++ [a]) u
  | [] => (append_nil _).symm ▸ (foldl_nil ▸ rfl)
  | _::_ => foldl_cons.symm ▸ concat_eq_foldl ▸ (append_cons u _ _) ▸ rfl


theorem flatten_eq_foldl_foldl {l: List (List α)}:
    l.flatten = l.foldl (fun acc u => u.foldl (fun acc a => acc ++ [a]) acc) [] :=
  flatten_eq_foldl_append ▸ congrArg
    (fun x => l.foldl x [])
    (funext (fun _ => funext (fun _ => concat_eq_foldl)))


theorem nodup_flatten {l: List (List α)}
  (h1: l.Pairwise Disjoint) (h2: ∀ u: List α, u ∈ l → u.Nodup):
    l.flatten.Nodup :=
  match l with
  | [] => nodup_nil
  | h::_ =>
    flatten_cons ▸ nodup_append.mpr ⟨
      h2 h mem_cons_self,
      nodup_flatten (pairwise_cons.mp h1).right
        (fun u hu => h2 u (mem_cons_of_mem h hu)),
      fun a ha _ hb eq =>
        have ⟨u, hu, hb⟩ := mem_flatten.mp hb
        have h_u_disjoint := (pairwise_cons.mp h1).left u hu
        h_u_disjoint a ha (eq ▸ hb)
    ⟩


theorem sublist_flatten_of_sublist {u v: List (List α)}:
    u.Sublist v → u.flatten.Sublist v.flatten
  | Sublist.slnil => Sublist.refl []
  | Sublist.cons (l₂ := t) l h => Sublist.trans
    (sublist_flatten_of_sublist h)
    (flatten_cons ▸ (sublist_append_right l t.flatten))
  | Sublist.cons₂ l h => (append_sublist_append_left l).mpr
    (sublist_flatten_of_sublist h)


theorem pair_sublist_flatten {a b: α} {l: List (List α)}
  (h: ∃ u v: List α, a ∈ u ∧ b ∈ v ∧ [u, v].Sublist l):
    [a, b].Sublist l.flatten :=
  have ⟨u, v, ha, hb, sub⟩ := h
  have s₁: [a, b].Sublist (u ++ v) := (singleton_sublist.mpr ha).append
    (singleton_sublist.mpr hb)
  have s₂: [u, v].flatten.Sublist l.flatten := sublist_flatten_of_sublist sub
  have flatten_append: [u, v].flatten = u ++ v := flatten_cons.symm ▸ flatten_cons.symm ▸
    flatten_nil.symm ▸ (append_nil _).symm ▸ rfl
  s₁.trans (flatten_append ▸ s₂)


theorem pair_getElem_sublist {l: List α} {i j: Nat}
  (hi: i < l.length) (hj: j < l.length) (h: i < j):
    [l[i], l[j]].Sublist l :=
  have ⟨a, t, hl⟩ := exists_cons_of_length_pos (Nat.zero_lt_of_lt hi)
  have length_l: l.length = t.length + 1 := hl ▸ length_cons
  have ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt h)
  match i with
  | 0 =>
    have htail: [t[v]].Sublist t := singleton_sublist.mpr (getElem_mem _)
    have htail': [l[j]].Sublist t := hv ▸ hl ▸ htail
    have a_eq: a = l[0] := hl ▸ rfl
    have c: [l[0], l[j]].Sublist (a::t) := a_eq ▸ (Sublist.cons₂ a htail'); hl ▸ c
  | u + 1 =>
    have u_lt: u < t.length := Nat.lt_of_add_lt_add_right (length_l ▸ hi)
    have v_lt: v < t.length := Nat.lt_of_add_lt_add_right (length_l ▸ hv ▸ hj)
    have hrec := pair_getElem_sublist u_lt v_lt (Nat.lt_of_add_lt_add_right (hv ▸ h))
    hl ▸ (Sublist.cons a (hv ▸ hrec))


theorem sublist_flatten_of_sublist_elem {l: List (List α)} {u: List α}
  (h: ∃ v: List α, v ∈ l ∧ u.Sublist v):
    u.Sublist l.flatten :=
  have ⟨_, hv, hu⟩ := h; hu.trans (List.sublist_flatten_of_mem hv)


theorem exists_pair_getElem_of_sublist {l: List α} {a b: α} (h: [a, b].Sublist l):
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


theorem idx_inj_of_nodup {l: List α} (h1: l.Nodup) {i j: Nat} (hi: i < l.length) (hj: j < l.length)
    (h2: l[i] = l[j]): i = j :=
  match Nat.lt_trichotomy i j with
  | .inl lt => False.elim (List.pairwise_iff_getElem.mp h1 i j hi hj lt h2)
  | .inr (.inl eq) => eq
  | .inr (.inr lt) => False.elim (List.pairwise_iff_getElem.mp h1 j i hj hi lt h2.symm)

end List
end


public section
namespace Vector

variable {α} {k: Nat}

def modify (v: Vector α k) (i: Fin k) (f: α → α): Vector α k :=
  ⟨v.toArray.modify i.val f, Eq.trans Array.size_modify v.size_toArray⟩


theorem get_modify_self {v: Vector α k} {i: Fin k} {f: α → α}:
    (v.modify i f).get i = f (v.get i) :=
  Array.getElem_modify_self f ((v.modify i f).size_toArray.symm ▸ i.isLt)


theorem get_modify_of_ne {v: Vector α k} {i j: Fin k} {f: α → α} (h: i ≠ j):
    (v.modify i f).get j = v.get j :=
  Array.getElem_modify_of_ne (Fin.val_ne_iff.mpr h) f ((v.modify i f).size_toArray.symm ▸ j.isLt)


theorem get_ext {v w: Vector α k} (h: ∀ i: Fin k, v.get i = w.get i): v = w :=
  Vector.ext (fun i hi => h ⟨i, hi⟩)


theorem get_replicate {a: α} {i: Fin k}: (replicate k a).get i = a :=
  have lt: i.val < (replicate k a).toArray.size :=
    ((replicate k a).size_toArray.symm) ▸ i.isLt
  Array.getElem_replicate lt


theorem modify_modify_self {v: Vector α k} {i: Fin k} {f g: α → α}:
    (v.modify i f).modify i g = v.modify i (g ∘ f) :=
  get_ext (fun j =>
    if eq: i = j then
        eq.symm ▸
        get_modify_self.symm ▸
        get_modify_self.symm ▸
        get_modify_self.symm ▸ rfl
    else
        (get_modify_of_ne eq).symm ▸
        (get_modify_of_ne eq).symm ▸
        (get_modify_of_ne eq).symm ▸ rfl
  )


theorem modify_modify_of_ne {v: Vector α k} {i j: Fin k} {f g: α → α} (h: i ≠ j):
    (v.modify i f).modify j g = (v.modify j g).modify i f :=
  get_ext (fun a =>
    if eqi: i = a then
      eqi ▸
      (get_modify_of_ne h.symm).symm ▸
      get_modify_self.symm ▸
      get_modify_self.symm ▸
      (get_modify_of_ne h.symm).symm ▸ rfl
    else if eqj: j = a then
      eqj ▸
      (get_modify_of_ne h).symm ▸
      get_modify_self.symm ▸
      get_modify_self.symm ▸
      (get_modify_of_ne h).symm ▸ rfl
    else
      (get_modify_of_ne eqi).symm ▸
      (get_modify_of_ne eqj).symm ▸
      (get_modify_of_ne eqj).symm ▸
      (get_modify_of_ne eqi).symm ▸ rfl
  )


theorem modify_comm {v: Vector α k} {i j: Fin k}
  {f: α → α} {g: α → α} (h: g ∘ f = f ∘ g):
    (v.modify i f).modify j g = (v.modify j g).modify i f :=
  if eq: i = j then
    eq ▸
    modify_modify_self.symm ▸
    modify_modify_self.symm ▸
    (congrArg _ h)
  else
    modify_modify_of_ne eq


theorem get_ofFn {f: Fin k → α} {i: Fin k}:
    (ofFn f).get i = f i :=
  Array.getElem_ofFn _


theorem get_mem {v: Vector α k} {i: Fin k}: v.get i ∈ v :=
    Vector.getElem_mem i.isLt


theorem exists_get_of_mem {v: Vector α k} {a: α} (h: a ∈ v):
    ∃ i: Fin k, a = v.get i :=
  have ⟨i, hi, hvi⟩ := Vector.mem_iff_getElem.mp h; ⟨⟨i, hi⟩, hvi.symm⟩


theorem getElem_toList' {v: Vector α k} {i: Fin k}:
    v.toList[i] = v.get i := Vector.getElem_toList (Vector.length_toList ▸ i.isLt)


theorem get_of_mem {v: Vector α k} {a: α} (h: a ∈ v):
    ∃ i: Fin k, v.get i = a :=
  have ⟨i, hi, eq⟩ := Vector.getElem_of_mem h
  ⟨⟨i, hi⟩, eq⟩


theorem pair_get_sublist_toList {v: Vector α k} {i j: Fin k} (h: ↑i < ↑j):
    [v.get i, v.get j].Sublist v.toList :=
  Vector.getElem_toList' ▸ Vector.getElem_toList' ▸ (List.pair_getElem_sublist _ _ h)


def cNone (v: Vector (Option α) k) := v.countP Option.isNone


theorem cNone_set {v: Vector (Option α) k} {i: Fin k} {x: α}
  (h: v.get i = none):
    (v.set i x).cNone + 1 = v.cNone :=
  have cond: v[i.val].isNone = true := Option.isNone_iff_eq_none.mpr h
  have le: v.countP Option.isNone ≥ 1 := Nat.one_le_of_lt (countP_pos_iff.mpr
    ⟨v.get i, getElem_mem _, Option.isNone_iff_eq_none.mpr h⟩)
  (congrArg (· + 1) (countP_set i.isLt)).trans (
    ite_cond_eq_true _ _ (eq_true cond) ▸ Nat.sub_add_comm le ▸
    (Nat.sub_add_cancel (Nat.le_add_right_of_le le)).symm ▸ rfl)


theorem cNone_le {v: Vector (Option α) k}: v.cNone ≤ k :=
  Vector.countP_le_size


theorem get_set_self {v: Vector α k} {i: Fin k} {a: α}:
    (v.set i a).get i = a :=
  getElem_set_self i.isLt


theorem get_set_of_ne {v: Vector α k} {i j: Fin k} {a: α} (h: i ≠ j):
    (v.set i a).get j = v.get j :=
  getElem_set_ne i.isLt j.isLt (Fin.val_ne_of_ne h)


theorem get_swap_of_ne {v: Vector α k} {i j m: Fin k} (hi: i ≠ m) (hj: j ≠ m):
    (v.swap i j).get m = v.get m :=
  getElem_swap_of_ne (Ne.symm (Fin.val_ne_of_ne hi)) (Ne.symm (Fin.val_ne_of_ne hj))


theorem get_swap_left {v: Vector α k} {i j: Fin k}:
    (v.swap i j).get i = v.get j :=
  getElem_swap_left i.isLt j.isLt


theorem get_swap_right {v: Vector α k} {i j: Fin k}:
    (v.swap i j).get j = v.get i :=
  getElem_swap_right i.isLt j.isLt


theorem get_pop {v: Vector α (k + 1)} {i: Fin k}:
    v.pop.get i = v.get i.castSucc :=
  getElem_pop i.isLt


theorem mem_of_mem_pop {v: Vector α (k + 1)} {a: α} (h: a ∈ v.pop):
    a ∈ v :=
  have ⟨_, hi⟩ := get_of_mem h
  (get_pop.symm.trans hi) ▸ get_mem

end Vector
end


@[expose]
public section
namespace Array

def flattenLists {α} {v: Array (List α)}: Array α :=
  v.foldl (fun acc l => l.foldl (fun acc a => acc.push a) acc) empty


theorem toList_flattenLists {α} {v: Array (List α)}:
    v.flattenLists.toList = v.foldl (fun acc l => l.foldl (fun acc a => acc ++ [a]) acc) [] :=
  (foldl_hom toList fun _ _ => (
    List.foldl_hom toList fun _ _ => Eq.symm toList_push
  )).symm


theorem toList_flattenLists_eq_flatten_toList {α} {v: Array (List α)}:
    v.flattenLists.toList = v.toList.flatten :=
  Eq.trans ((foldl_toList _) ▸ toList_flattenLists) List.flatten_eq_foldl_foldl.symm


def compose (v w: Array Nat) :=
  w.map (fun i => v.getD i 0)


theorem size_compose {v w: Array Nat}: (v.compose w).size = w.size :=
  Array.size_map


theorem getElem_compose {v w: Array Nat} {i: Nat} (hi: i < w.size) (hwi: w[i] < v.size):
    (v.compose w)[i]'(size_compose.symm ▸ hi) = v[w[i]] :=
  (getElem_map _ _) ▸ (getElem_eq_getD 0).symm


theorem mem_compose_of_mem {v w: Array Nat} {n: Nat} (h1: n ∈ v)
  (h2: ∀ i: Nat, i < v.size → i ∈ w): n ∈ v.compose w :=
  have ⟨i, hi, eq⟩ := getElem_of_mem h1
  mem_map.mpr ⟨i, h2 i hi, getElem_eq_getD 0 ▸ eq⟩


theorem compose_nodup {v w: Array Nat} (h1: v.toList.Nodup) (h2: w.toList.Nodup)
  (h3: ∀ i: Nat, i ∈ w → i < v.size):
    (v.compose w).toList.Nodup :=
  List.pairwise_iff_getElem.mpr (fun i j hi hj hij eq =>
    have hi: i < w.size := size_map ▸ length_toList ▸ hi
    have hj: j < w.size := size_map ▸ length_toList ▸ hj
    have hwi: w[i] < v.size := h3 w[i] (getElem_mem hi)
    have hwj: w[j] < v.size := h3 w[j] (getElem_mem hj)
    have eqi: (v.compose w).toList[i] = v[w[i]] := getElem_compose hi hwi
    have eqj: (v.compose w).toList[j] = v[w[j]] := getElem_compose hj hwj
    have eq: v[w[i]] = v[w[j]] := eqi ▸ eqj ▸ eq
    match Nat.lt_trichotomy w[i] w[j] with
    | .inl ineq => List.pairwise_iff_getElem.mp h1 w[i] w[j] hwi hwj ineq eq
    | .inr (.inl eq) => List.pairwise_iff_getElem.mp h2 i j hi hj hij eq
    | .inr (.inr ineq) => List.pairwise_iff_getElem.mp h1 w[j] w[i] hwj hwi ineq eq.symm
  )


theorem compose_sublist_pair {v w: Array Nat} {a b: Nat} (h1: [a, b].Sublist w.toList)
  (h2: a < v.size) (h3: b < v.size):
    [v[a], v[b]].Sublist (v.compose w).toList :=
  have ⟨ia, ib, hia, hib, eqa, eqb⟩ := List.exists_pair_getElem_of_sublist h1
  have hib: ib < w.size := length_toList ▸ hib
  have eqa: w[ia] = a := eqa; have eqb: w[ib] = b := eqb
  have size_eq: (v.compose w).toList.length = w.toList.length :=
    length_toList ▸ length_toList ▸ size_compose
  have hia': ia < (v.compose w).toList.length := size_eq ▸ Nat.lt_trans hia hib
  have hib': ib < (v.compose w).toList.length := size_eq ▸ hib
  have veqa: v[w[ia]] = v[a] := getElem_congr_idx eqa
  have veqb: v[w[ib]] = v[b] := getElem_congr_idx eqb
  have eqa': (v.compose w).toList[ia] = v[a] :=
    veqa ▸ getElem_toList _ ▸ (getElem_compose (Nat.lt_trans hia hib) (eqa ▸ h2))
  have eqb': (v.compose w).toList[ib] = v[b] :=
    veqb ▸ getElem_toList _ ▸ (getElem_compose hib (eqb ▸ h3))
  eqa' ▸ eqb' ▸ List.pair_getElem_sublist hia' hib' hia


theorem getD_eq_default {α} (v: Array α) (d: α) {n: Nat} (h: v.size ≤ n): v.getD n d = d :=
  dite_cond_eq_false (eq_false (Nat.not_lt_of_le h))


theorem back?_eq_back {α} {v: Array α} (h: 0 < v.size): v.back? = some v.back :=
  (back?_eq_getElem?.trans (getElem?_eq_getElem (Nat.sub_one_lt_of_lt h))).trans
    (congrArg some (back_eq_getElem _).symm)

end Array
end


@[expose]
public section
namespace Option

variable {α}

def allP (p: α → Prop): (o: Option α) → Prop
  | none => True
  | some a => p a


theorem allP_mp {p q: α → Prop} {o: Option α} (h1: o.allP p) (h2: ∀ a: α, p a → q a): o.allP q :=
  match o with
  | none => True.intro
  | some a => h2 a h1

end Option
end


@[expose]
public section
namespace Except

variable {α β}

def allP (p: α → Prop): (e: Except β α) → Prop
  | Except.error _ => True
  | Except.ok a => p a


def allEP (p: β → Prop): (e: Except β α) → Prop
  | Except.error e => p e
  | Except.ok _ => True


theorem allP_mp {p q: α → Prop} {e: Except β α} (h1: e.allP p) (h2: ∀ a: α, p a → q a): e.allP q :=
  match e with
  | Except.error _ => True.intro
  | Except.ok a => h2 a h1


theorem allP_forall {ι} {p: ι → α → Prop}:
    {e: Except β α} → (∀ i, e.allP (p i)) ↔ (e.allP (fun a => ∀ i, p i a))
  | Except.error _ => ⟨fun _ => True.intro, fun _ _ => True.intro⟩
  | Except.ok _ => ⟨id, id⟩


theorem allP_imp {c: Prop} {p: α → Prop}:
    {e: Except β α} → (c → e.allP p) ↔ (e.allP (fun a => c → p a))
  | Except.error _ => ⟨fun _ => True.intro, fun _ _ => True.intro⟩
  | Except.ok _ => ⟨id, id⟩


theorem allP_and {p q: α → Prop}: {e: Except β α} → e.allP p ∧ e.allP q ↔ e.allP (fun a => p a ∧ q a)
  | Except.error _ => ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩
  | Except.ok _ => ⟨id, id⟩


theorem pure_def {a: α}: (pure a: Except β α) = Except.ok a := rfl

end Except
end


public theorem Fin.foldl_induction {α} {n: Nat} (motive: α → Nat → Prop)
  {init: α} (h0: motive init 0) {f: α → Fin n → α}
  (hr: ∀ (a: α) (i: Fin n), motive a i.val → motive (f a i) i.val.succ):
    motive (Fin.foldl n f init) n :=
  match n with
  | 0 => Fin.foldl_zero _ _ ▸ h0
  | n + 1 =>
    have hrec: motive (Fin.foldl n (fun a i => f a i.castSucc) init) n :=
      Fin.foldl_induction _ h0 (fun a i ha => hr a i.castSucc ha)
    Fin.foldl_succ_last _ _ ▸ hr _ (last n) hrec


public theorem Fin.foldlM_induction {α m} [Monad m] [LawfulMonad m] {n: Nat} (motive: m α → Nat → Prop)
  {init: α} (h0: motive (pure init) 0) {f: α → Fin n → m α}
  (hr: ∀ (a: m α) (i: Fin n), motive a i.val → motive (a >>= (f · i)) i.val.succ):
    motive (Fin.foldlM n f init) n :=
  match n with
  | 0 =>  (congrFun (Fin.foldlM_zero f) init).symm.subst (motive := fun w => motive w 0) h0
  | n + 1 =>
    have hrec: motive (Fin.foldlM n (fun a i => f a i.castSucc) init) n :=
      Fin.foldlM_induction _ h0 (fun a i ha => hr a i.castSucc ha)
    Fin.foldlM_succ_last (m := m) _ ▸ hr _ (last n) hrec
