module

import AutoKchp.Internal.Util
public import AutoKchp.Internal.TotalOrder

/-
All the machinery to handle the implicit binary tree
-/
abbrev left (x: Nat): Nat := 2 * x + 1


theorem lt_left {x: Nat}: x < left x :=
  Nat.lt_succ_of_le (Nat.le_mul_of_pos_left x (of_decide_eq_true rfl))


abbrev right (x: Nat): Nat := 2 * x + 2


theorem lt_right {x: Nat}: x < right x :=
  Nat.lt_succ_of_lt lt_left


theorem left_ne_right {x: Nat}: left x ≠ right x :=
  Nat.ne_of_lt (Nat.add_lt_add_left (of_decide_eq_true rfl) (2 * x))


def parent (x: Nat): Nat := (x - 1) / 2


theorem parent_le {x: Nat}: parent x ≤ x :=
  Nat.le_trans (Nat.div_le_self (x - 1) 2) (Nat.sub_le x 1)


theorem parent_eq_self {x: Nat} (h: parent x = x): x = 0 :=
  match x with
  | 0 => rfl
  | x + 1 => False.elim (Nat.not_succ_le_self x (Nat.le_trans (Nat.le_of_eq h.symm)
    (Nat.div_le_self x 2)))


theorem parent_left {x: Nat}: parent (left x) = x :=
  have concl: (2 * x + 1 - 1) / 2 = x :=
    Nat.add_sub_cancel (2 * x) 1 ▸ Nat.mul_comm 2 x ▸ Nat.mul_div_cancel x (of_decide_eq_true rfl);
  concl


theorem parent_right {x: Nat}: parent (right x) = x :=
  have concl: (2 * x + 2 - 1) / 2 = x :=
    Nat.add_one_sub_one (2 * x + 1) ▸ Nat.mul_comm 2 x ▸ Nat.div_eq_of_lt_le
      (Nat.le_succ (x * 2))
      (Nat.add_mul x 1 2 ▸ Nat.add_lt_add_left (of_decide_eq_true rfl) (x * 2))
  concl


theorem eq_left_or_right_parent {x: Nat} (h: x > 0): x = left (parent x) ∨ x = right (parent x) :=
  if eq: (x - 1) % 2 = 0 then
    Or.inl (left.eq_def (parent x) ▸ Nat.mul_div_self_eq_mod_sub_self ▸ eq ▸
      (Nat.sub_add_cancel (Nat.one_le_of_lt h)).symm)
  else
    have mod_eq: (x - 1) % 2 = 1 := Nat.le_antisymm
      (Nat.le_of_lt_succ (Nat.mod_lt _ (of_decide_eq_true rfl)))
      (Nat.one_le_iff_ne_zero.mpr eq)
    have x_ge: x ≥ 2 := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne
      (Nat.one_le_of_lt h) (fun eq => (of_decide_eq_false rfl) (eq.symm ▸ mod_eq)))
    Or.inr (right.eq_def (parent x) ▸ Nat.mul_div_self_eq_mod_sub_self ▸ mod_eq.symm ▸
      ((Nat.sub_eq_iff_eq_add x_ge).mp rfl))


inductive Side where
  | left
  | right


def Side.other: Side → Side
  | Side.left => Side.right
  | Side.right => Side.left


theorem Side.other_other: (s: Side) → s.other.other = s
  | Side.left => rfl | Side.right => rfl


theorem Side.ne_other: {s: Side} → s ≠ s.other
  | Side.left => fun eq => nomatch eq
  | Side.right => fun eq => nomatch eq


theorem Side.induction (s: Side) (motive: Side → Prop)
  (h1: motive s) (h2: motive s.other) {s₂: Side}:
    motive s₂ :=
  match s with
  | Side.left => match s₂ with
    | Side.left => h1
    | Side.right => h2
  | Side.right => match s₂ with
    | Side.left => h2
    | Side.right => h1


def child (x: Nat): (s: Side) → Nat
  | Side.left => left x
  | Side.right => right x


theorem lt_child {x: Nat}: {s: Side} → x < child x s
  | Side.left => lt_left
  | Side.right => lt_right


theorem parent_child {x: Nat}: {s: Side} → parent (child x s) = x
  | Side.left => parent_left
  | Side.right => parent_right


theorem eq_child_parent {x: Nat} (h: x > 0): ∃ s: Side, x = child (parent x) s :=
  match eq_left_or_right_parent h with
  | .inl eqlp => ⟨Side.left, eqlp⟩
  | .inr eqrp => ⟨Side.right, eqrp⟩


theorem child_inj_s {x: Nat} {s₁ s₂: Side} (h: child x s₁ = child x s₂):
    s₁ = s₂ :=
  match s₁ with
  | Side.left => match s₂ with
    | Side.left => rfl
    | Side.right => False.elim (left_ne_right h)
  | Side.right => match s₂ with
    | Side.left => False.elim (left_ne_right h.symm)
    | Side.right => rfl


inductive ancestor: Nat → Nat → Prop
  | refl: (x: Nat) → ancestor x x
  | parent: {x y: Nat} → ancestor x y → ancestor (parent x) y


theorem ancestor_refl (x: Nat): ancestor x x := ancestor.refl x


theorem ancestor_child (x: Nat) (s: Side): ancestor x (child x s) :=
  parent_child.subst (motive := fun w => ancestor w (child x s))
    (ancestor.parent (ancestor.refl (child x s)))


theorem ancestor_trans {x y z: Nat} (h1: ancestor x y) (h2: ancestor y z):
    ancestor x z :=
  match h1 with
    | ancestor.refl _ => h2
    | ancestor.parent a => ancestor.parent (ancestor_trans a h2)


theorem eq_or_child_ancestor_of_ancestor {x y: Nat} (h: ancestor x y):
    x = y ∨ ∃ s: Side, (ancestor (child x s) y) :=
  match h with
  | ancestor.refl _ => Or.inl rfl
  | ancestor.parent (x := u) a =>
    if eq: u = 0 then
      have concl: 0 = y ∨ ∃ s, (ancestor (child 0 s) y) :=
        eq ▸ (eq_or_child_ancestor_of_ancestor a)
      eq ▸ concl
    else
      have ⟨s, eqs⟩ := eq_child_parent (Nat.zero_lt_of_ne_zero eq)
      Or.inr ⟨s, eqs ▸ a⟩


theorem eq_or_ancestor_parent_of_ancestor {x y: Nat} (h: ancestor x y):
    x = y ∨ (ancestor x (parent y)) :=
  match h with
    | ancestor.refl _ => Or.inl rfl
    | ancestor.parent (x := u) (y := v) a => match eq_or_ancestor_parent_of_ancestor a with
      | .inl eq => Or.inr (eq ▸ ancestor.refl (parent u))
      | .inr a2 => Or.inr (ancestor.parent a2)


theorem le_of_ancestor {x y: Nat} (h: ancestor x y): x ≤ y :=
  match h with
    | ancestor.refl _ => Nat.le_refl _
    | ancestor.parent a => Nat.le_trans parent_le (le_of_ancestor a)


theorem child_not_ancestor {x: Nat} {s: Side}: ¬ancestor (child x s) x :=
  fun a => Nat.not_le_of_lt lt_child (le_of_ancestor a)


theorem parent_ancestor_parent {i j: Nat} (h: ancestor i j):
    ancestor (parent i) (parent j) :=
  match h with
  | ancestor.refl _ => ancestor.refl (parent i)
  | ancestor.parent a => ancestor.parent (parent_ancestor_parent a)


theorem two_ancestors {i j k: Nat} (hi: ancestor i k) (hj: ancestor j k):
    ancestor i j ∨ ancestor j i :=
  match hi with
  | ancestor.refl _ => Or.inr hj
  | ancestor.parent (x := u) ai => match hj with
    | ancestor.refl _ => Or.inl (ancestor.parent ai)
    | ancestor.parent (x := v) aj => match two_ancestors ai aj with
      | .inl a => Or.inl (parent_ancestor_parent a)
      | .inr a => Or.inr (parent_ancestor_parent a)


theorem sibling_not_ancestor {s: Side} {x: Nat}:
    ¬ancestor (child x s) (child x s.other) :=
  fun a => match eq_or_ancestor_parent_of_ancestor a with
    | .inl eq => Side.ne_other (child_inj_s eq)
    | .inr a2 => Nat.not_le_of_lt lt_child (le_of_ancestor (parent_child ▸ a2))


theorem not_both_siblings_ancestor {s: Side} {x y: Nat}:
    ancestor (child x s) y → ancestor (child x s.other) y → False :=
  fun a1 a2 => match two_ancestors a1 a2 with
  | .inl a => sibling_not_ancestor a
  | .inr a => sibling_not_ancestor ((Side.other_other s).substr a)


theorem zero_ancestor (x: Nat): ancestor 0 x :=
  match x with
  | 0 => ancestor.refl 0
  | y + 1 => ancestor_trans (zero_ancestor (parent (y + 1)))
    (ancestor.parent (ancestor.refl (y + 1)))
  termination_by x
  decreasing_by exact Nat.lt_of_le_of_ne parent_le (fun eq => nomatch parent_eq_self eq)


instance instDecidableAncestor {x y: Nat}: Decidable (ancestor x y) :=
  if lt: y < x then
    Decidable.isFalse (fun a => Nat.not_le_of_lt lt (le_of_ancestor a))
  else
    if eq: x = y then
      Decidable.isTrue (eq ▸ ancestor.refl x)
    else
      match instDecidableAncestor (x := x) (y := parent y) with
        | Decidable.isFalse na => Decidable.isFalse
          (fun a => match eq_or_ancestor_parent_of_ancestor a with
            | .inl eq2 => eq eq2
            | .inr a2 => na a2
          )
        | Decidable.isTrue a => Decidable.isTrue
          (ancestor_trans a (ancestor.parent (ancestor.refl _)))
  termination_by y
  decreasing_by exact Nat.lt_of_le_of_ne parent_le (fun eq2 => Nat.ne_zero_of_lt (b := x)
    (Nat.lt_of_le_of_ne (Nat.le_of_not_lt lt) eq) (parent_eq_self eq2))


/-
Heap definition, fundamental sift-down routine
-/
def heap {α} [TotalOrd α] {n: Nat} (v: Vector α n) (i: Fin n): Prop :=
  ∀ s: Side, ∀ h: child i s < n, v.get i ≤ v.get ⟨child i s, h⟩ ∧
    heap v ⟨child i s, h⟩
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt lt_child


theorem heap_of_ancestor_heap {α} [TotalOrd α] {n: Nat} {v: Vector α n} {i j: Fin n}
  (a: ancestor i j) (h: heap v i):
    heap v j :=
  match eq_or_child_ancestor_of_ancestor a with
  | .inl eq => (Fin.eq_of_val_eq eq).subst h
  | .inr ⟨s, a⟩ =>
    have lt: child i s < n := Nat.lt_of_le_of_lt (le_of_ancestor a) j.isLt
    heap_of_ancestor_heap (i := ⟨child i s, lt⟩) a ((heap.eq_def v i ▸ h) s lt).right
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt lt_child


def almostHeap {α} [TotalOrd α] {n: Nat} (v: Vector α n) (i: Fin n): Prop :=
  ∀ s: Side, ∀ h: child i s < n, heap v ⟨child i s, h⟩


inductive Swap where
  | noSwap
  | swap: (s: Side) → Swap


def computeSwap {α} [TotalOrd α] (parent: α) (children: Side → α): Swap :=
  if children Side.left ≤ children Side.right then
    if parent ≤ children Side.left then Swap.noSwap
    else Swap.swap Side.left
  else
    if parent ≤ children Side.right then Swap.noSwap
    else Swap.swap Side.right


theorem of_computeSwap_eq_noSwap {α} [t: TotalOrd α]
  {parent: α} {children: Side → α} (h: computeSwap parent children = Swap.noSwap):
    ∀ s: Side, parent ≤ children s :=
  if le1: children Side.left ≤ children Side.right then
    if le2: parent ≤ children Side.left then
      fun
        | Side.left => le2
        | Side.right => t.le_trans le2 le1
    else
      nomatch (if_neg le2).symm.trans ((if_pos le1).symm.trans h)
  else
    if le2: parent ≤ children Side.right then
      fun
        | Side.left => t.le_trans le2
          ((t.le_total (children Side.left) (children Side.right)).resolve_left le1)
        | Side.right => le2
    else
      nomatch (if_neg le2).symm.trans ((if_neg le1).symm.trans h)


theorem of_computeSwap_eq_swap {α} [t: TotalOrd α]
  {parent: α} {children: Side → α} {s: Side} (h: computeSwap parent children = Swap.swap s):
    children s ≤ parent ∧ children s ≤ children s.other :=
  if le1: children Side.left ≤ children Side.right then
    if le2: parent ≤ children Side.left then
      nomatch (if_pos le2).symm.trans ((if_pos le1).symm.trans h)
    else
      match s with
        | Side.left => ⟨(t.le_total parent (children Side.left)).resolve_left le2, le1⟩
        | Side.right => nomatch (if_neg le2).symm.trans ((if_pos le1).symm.trans h)
  else
    if le2: parent ≤ children Side.right then
      nomatch (if_pos le2).symm.trans ((if_neg le1).symm.trans h)
    else
      match s with
        | Side.left =>  nomatch (if_neg le2).symm.trans ((if_neg le1).symm.trans h)
        | Side.right => ⟨
            (t.le_total parent (children Side.right)).resolve_left le2,
            (t.le_total _ _).resolve_left le1
          ⟩


def siftFrom {α} [TotalOrd α] {n: Nat} (v: Vector α n) (i: Fin n): Vector α n :=
  let left := left i
  let right := right i
  if rlt: right < n then
    let fin_child (s: Side): Fin n := ⟨child i s, match s with
      | Side.left => Nat.lt_of_succ_lt rlt | Side.right => rlt⟩
    match computeSwap (v.get i) (fun s => v.get (fin_child s)) with
    | Swap.noSwap => v
    | Swap.swap s => siftFrom (v.swap i (fin_child s)) (fin_child s)
  else if llt: left < n then
    let fin_left: Fin n := ⟨left, llt⟩
    if v.get i ≤ v.get fin_left then v
    else v.swap i fin_left
  else
    v
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt (s.casesOn lt_left lt_right)


def siftFrom_only_descendants {α} [TotalOrd α] {n: Nat} {v: Vector α n}
  {i j: Fin n} (h: ¬ancestor i j):
    (siftFrom v i).get j = v.get j :=
  have nej: i ≠ j := fun eq => h (eq ▸ ancestor_refl i)
  siftFrom.eq_def v i ▸ if rlt: right i < n then
    let fin_child (s: Side): Fin n := ⟨child i s, match s with
      | Side.left => Nat.lt_of_succ_lt rlt | Side.right => rlt⟩
    let swap := computeSwap (v.get i) (fun s => v.get (fin_child s))
    have concl: (match swap with
      | Swap.noSwap => v
      | Swap.swap s => siftFrom (v.swap i (fin_child s)) (fin_child s)
      ).get j = v.get j := match swap with
      | Swap.noSwap => rfl
      | Swap.swap s =>
        have hsw: (v.swap i (fin_child s)).get j = v.get j :=
          Vector.get_swap_of_ne nej (Fin.ne_of_val_ne
            (fun eq => h (eq ▸ ancestor_child i s)))
        Eq.trans (siftFrom_only_descendants
        (fun a => h (ancestor_trans (ancestor_child i s) a))) hsw
    dif_pos rlt ▸ concl
  else if llt: left i < n then
    let fin_left: Fin n := ⟨left i, llt⟩
    have hswl: (v.swap i fin_left).get j = v.get j :=
      Vector.get_swap_of_ne nej (Fin.ne_of_val_ne
        (fun eq => h (eq ▸ ancestor_child i Side.left)))
    dif_neg rlt ▸ dif_pos llt ▸ iteInduction (motive := fun (w: Vector α n) => w.get j = v.get j)
        (fun _ => rfl) (fun _ => hswl)
  else
    dif_neg rlt ▸ dif_neg llt ▸ rfl
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt (s.casesOn lt_left lt_right)


theorem heap_only_descendants {α} [TotalOrd α] {n: Nat} {v₁ v₂: Vector α n} {i: Fin n}
  (h: ∀ j: Fin n, ancestor i j → v₁.get j = v₂.get j):
    heap v₁ i → heap v₂ i :=  fun hh =>
  have hh := heap.eq_def v₁ i ▸ hh
  heap.eq_def v₂ i ▸ fun s hc =>
    ⟨
      h i (ancestor_refl i) ▸ h ⟨(child i s), hc⟩ (ancestor_child i s) ▸ (hh s hc).left,
      heap_only_descendants (fun j hj => h j (ancestor_trans (ancestor_child i s) hj))
        (hh s hc).right
    ⟩
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt lt_child


theorem siftFrom_sibling_heap {α} [TotalOrd α] {n: Nat} {v: Vector α n} {i: Fin n}
  {s: Side} (h: ∀ lt: child i s.other < n, heap v ⟨child i s.other, lt⟩):
    ∀ lt1: child i s < n, ∀ lt2: child i s.other < n,
      heap (siftFrom v ⟨child i s, lt1⟩) ⟨child i s.other, lt2⟩ :=
  fun _ lt2 =>
    heap_only_descendants (v₁ := v) (fun _ hj =>
      (siftFrom_only_descendants (fun a => not_both_siblings_ancestor a hj)).symm
    ) (h lt2)


theorem swap_lt_heap {α} [TotalOrd α] {n: Nat} {v: Vector α n} {i j k: Fin n}
  (h: heap v k) (hi: i < k) (hj: j < k):
    heap (v.swap i j) k :=
  heap_only_descendants (fun p a =>
    have ine: i ≠ p := Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (le_of_ancestor a)))
    have jne: j ≠ p := Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hj (le_of_ancestor a)))
    (Vector.get_swap_of_ne ine jne).symm
  ) h


theorem swap_self_almostHeap {α} [TotalOrd α] {n: Nat} {v: Vector α n} {i j: Fin n}
  (h: heap v j) (hi: i < j):
    almostHeap (v.swap i j) j :=
  have h := Eq.mpr (heap.eq_def v j).symm h
  fun s hl => swap_lt_heap (h s hl).right (Nat.lt_trans hi lt_child) lt_child


theorem swap_sibling_heap {α} [TotalOrd α] {n: Nat} {v: Vector α n} {i: Fin n}
  {s: Side} (h: ∀ lt2: child i s.other < n, heap v ⟨child i s.other, lt2⟩)
  (lt: child i s < n):
    ∀ lt2: child i s.other < n, heap (v.swap i (child i s)) ⟨child i s.other, lt2⟩ :=
  fun lt2 => heap_only_descendants (fun j a =>
    (Vector.get_swap_of_ne (i := i) (j := ⟨child i s, lt⟩)
      (fun eq => child_not_ancestor (ancestor_trans a (eq ▸ ancestor_refl i)))
      (fun eq => not_both_siblings_ancestor (eq ▸ ancestor_refl j) a)).symm
  ) (h lt2)


theorem heap_of_almostHeap {α} [TotalOrd α] {n: Nat} {v: Vector α n} {k: Fin n}
  (h1: almostHeap v k)
  (h2: ∀ (s: Side) (hs: child k s < n), v.get k ≤ v.get ⟨child k s, hs⟩):
    heap v k :=
  heap.eq_def v k ▸ fun s hs => ⟨h2 s hs, h1 s hs⟩


theorem get_parent_siftFrom_swap {α} [TotalOrd α] (s: Side)
  {n: Nat} {v: Vector α n} {i: Fin n}:
    ∀ h: child i s < n, (siftFrom (v.swap i (child i s)) ⟨child i s, h⟩).get i =
      v.get ⟨child i s, h⟩ :=
  fun h => (siftFrom_only_descendants child_not_ancestor).trans
    (Vector.get_swap_left (i := i) (j := ⟨child i s, h⟩))


theorem get_siftFrom_self {α} [TotalOrd α] {n: Nat} {v: Vector α n} {i: Fin n}:
    (fun w => w = v.get i ∨ ∃ (s: Side) (h: child i s < n), w = v.get ⟨child i s, h⟩)
    ((siftFrom v i).get i) :=
  siftFrom.eq_def v i ▸ if rlt: right i < n then
    let fin_child (s: Side): Fin n := ⟨child i s, match s with
      | Side.left => Nat.lt_of_succ_lt rlt | Side.right => rlt⟩
    let swap := computeSwap (v.get i) (fun s => v.get (fin_child s))
    have concl: (fun w => w = v.get i ∨ ∃ (s: Side) (h: child i s < n), w = v.get ⟨child i s, h⟩)
      ((match swap with
      | Swap.noSwap => v
      | Swap.swap s => siftFrom (v.swap i (fin_child s)) (fin_child s)
      ).get i) := match swap with
      | Swap.noSwap => Or.inl rfl
      | Swap.swap s => Or.inr ⟨s, (fin_child s).isLt, get_parent_siftFrom_swap s _⟩
    dif_pos rlt ▸ concl
  else
    dif_neg rlt ▸ if llt: left i < n then
      dif_pos llt ▸ iteInduction  (motive := fun (x: Vector α n) =>
        (fun w => w = v.get i ∨ ∃ (s: Side) (h: child i s < n), w = v.get ⟨child i s, h⟩) (x.get i))
        (fun _ => Or.inl rfl)
        (fun _ => Or.inr ⟨Side.left, llt, Vector.get_swap_left⟩)
    else
      dif_neg llt ▸ Or.inl rfl


theorem get_child_siftFrom_swap {α} [TotalOrd α] (s: Side)
  {n: Nat} {v: Vector α n} {i: Fin n}:
    ∀ h: child i s < n, heap v ⟨child i s, h⟩ → (fun w => w = v.get i ∨ w ≥ v.get ⟨child i s, h⟩)
      ((siftFrom (v.swap i (child i s)) ⟨child i s, h⟩).get ⟨child i s, h⟩) := fun h hh =>
  (get_siftFrom_self (v := v.swap i (child i s)) (i := ⟨child i s, h⟩)).casesOn
    (fun eq => Or.inl (eq.trans (Vector.get_swap_right (i := i) (j := ⟨child i s, h⟩))))
    (fun ⟨s2, hs2, eq⟩ => Or.inr (
      eq ▸ (Vector.get_swap_of_ne (i := i) (j := ⟨child i s, h⟩) (m := ⟨child (child i s) s2, hs2⟩)
        (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_trans lt_child lt_child)))
        (Fin.ne_of_val_ne (Nat.ne_of_lt lt_child))).symm ▸
        ((heap.eq_def v _ ▸ hh) s2 hs2).left
    ))

theorem get_sibling_siftFrom_swap {α} [TotalOrd α] {s: Side}
  {n: Nat} {v: Vector α n} {i: Fin n}:
    ∀ h1: child i s < n, ∀ h2: child i s.other < n,
      (siftFrom (v.swap i (child i s)) ⟨child i s, h1⟩).get ⟨child i s.other, h2⟩ =
        v.get ⟨child i s.other, h2⟩ :=
  fun h1 _ => (siftFrom_only_descendants
    (fun a => not_both_siblings_ancestor a (ancestor_refl _))).trans
      (Vector.get_swap_of_ne (i := i) (j := ⟨child i s, h1⟩)
        (Fin.ne_of_val_ne (Nat.ne_of_lt lt_child))
        (Fin.ne_of_val_ne (fun eq => Side.ne_other (child_inj_s eq)))
      )


theorem siftFrom_correct {α} [t: TotalOrd α]
  {n: Nat} {v: Vector α n} {i: Fin n} (h: almostHeap v i):
    heap (siftFrom v i) i :=
  if rlt: right i < n then
    let fin_child (s: Side): Fin n := ⟨child i s, match s with
      | Side.left => Nat.lt_of_succ_lt rlt | Side.right => rlt⟩

    let ssw (s: Side) := siftFrom (v.swap i (fin_child s)) (fin_child s)
    have hrec (s: Side): heap (ssw s) (fin_child s) :=
      siftFrom_correct (swap_self_almostHeap
        (h s (fin_child s).isLt) (Fin.lt_def.mpr ((lt_child))))

    have sibling_heap (s: Side): heap (ssw s) (fin_child s.other) :=
      (siftFrom_sibling_heap
        (fun _ => swap_sibling_heap (h s.other) (fin_child s).isLt (fin_child s.other).isLt))
      (fin_child s).isLt (fin_child s.other).isLt
    have almost_heap (s: Side): almostHeap (ssw s) i := fun _ _ =>
      s.induction (fun s2 => heap (ssw s) (fin_child s2)) (hrec s) (sibling_heap s)

    have get_parent (s: Side): (ssw s).get i = v.get (fin_child s) :=
      get_parent_siftFrom_swap s (fin_child s).isLt
    have get_child (s: Side): (ssw s).get (fin_child s) = v.get i
        ∨ (ssw s).get (fin_child s) ≥ v.get (fin_child s) :=
      get_child_siftFrom_swap s (fin_child s).isLt (h s (fin_child s).isLt)
    have get_sibling (s: Side): (ssw s).get (fin_child s.other) = v.get (fin_child s.other) :=
       get_sibling_siftFrom_swap (i := i) (fin_child s).isLt (fin_child s.other).isLt

    let swap := computeSwap (v.get i) (fun s => v.get (fin_child s))
    have concl: heap (match swap with
      | Swap.noSwap => v
      | Swap.swap s => siftFrom (v.swap i (fin_child s)) (fin_child s)
      ) i := match eqsw: swap with
      | Swap.noSwap => heap_of_almostHeap h (fun s _ => of_computeSwap_eq_noSwap eqsw s)
      | Swap.swap s =>
        have hsw := of_computeSwap_eq_swap eqsw
        heap_of_almostHeap (almost_heap s) (fun s₂ _ => get_parent s ▸
          s.induction (fun w => v.get (fin_child s) ≤ (ssw s).get (fin_child w))
            (match (get_child s) with
              | .inl eqi => t.le_trans hsw.left (eqi ▸ t.le_refl (v.get i))
              | .inr le => le)
            ((congrArg (fun x => v.get (fin_child s) ≤ x) (get_sibling s)).mpr
                hsw.right)
          )

    siftFrom.eq_def v i ▸ dif_pos rlt ▸ concl
  else if llt: left i < n then
    let fin_left: Fin n := ⟨child i Side.left, llt⟩
    siftFrom.eq_def v i ▸ dif_neg rlt ▸ dif_pos llt ▸
      iteInduction (motive := fun (w: Vector α n) => heap w i)
        (fun le => heap_of_almostHeap h (fun s hs => match s with
          | Side.left => le
          | Side.right => False.elim (rlt hs)
        ))
        (fun nle => (heap.eq_def (v.swap i fin_left) i).mpr fun s hs => match s with
          | Side.left => ⟨
              have concl: (v.swap i fin_left).get i ≤ (v.swap i fin_left).get fin_left :=
                (Vector.get_swap_left (j := fin_left)).symm ▸
                (Vector.get_swap_right (j := fin_left)).symm ▸
                  (t.le_total (v.get i) (v.get fin_left)).resolve_left nle
              concl,
              (heap.eq_def (v.swap i fin_left) _).mpr fun s hs =>
                False.elim (rlt (Nat.lt_of_le_of_lt (Nat.add_one_le_of_lt lt_child) hs))
            ⟩
          | Side.right => False.elim (rlt hs)
        )
  else
    heap.eq_def (siftFrom v i) i ▸ siftFrom.eq_def v i ▸
    dif_neg rlt ▸ dif_neg llt ▸ (fun s hs => match s with
      | Side.left => False.elim (llt hs)
      | Side.right => False.elim (rlt hs)
    )
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt (s.casesOn lt_left lt_right)


theorem siftFrom_perm {α} [TotalOrd α] {n: Nat} {v: Vector α n} {i: Fin n}:
    v.Perm (siftFrom v i) :=
  siftFrom.eq_def v i ▸ if rlt: right i < n then
    let fin_child (s: Side): Fin n := ⟨child i s, match s with
      | Side.left => Nat.lt_of_succ_lt rlt | Side.right => rlt⟩
    let swap := computeSwap (v.get i) (fun s => v.get (fin_child s))
    have concl: v.Perm (match swap with
      | Swap.noSwap => v
      | Swap.swap s => siftFrom (v.swap i (fin_child s)) (fin_child s)
     ) := match swap with
      | Swap.noSwap => Vector.Perm.rfl
      | Swap.swap s => Vector.Perm.trans (Vector.swap_perm i.isLt (fin_child s).isLt).symm siftFrom_perm
    dif_pos rlt ▸ concl
  else if llt: left i < n then
    let fin_left: Fin n := ⟨left i, llt⟩
    dif_neg rlt ▸ dif_pos llt ▸ iteInduction (motive := fun (w: Vector α n) => v.Perm w)
        (fun _ => Vector.Perm.rfl) (fun _ => (Vector.swap_perm _ _).symm)
  else
    dif_neg rlt ▸ dif_neg llt ▸ Vector.Perm.rfl
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt (s.casesOn lt_left lt_right)

/-
Construct a min-heap in-place in O(n) time
-/
def heapifyFrom {α} [TotalOrd α] {n: Nat} (v: Vector α n):
    (i: Nat) → i ≤ n → Vector α n
  | 0 => fun _ => v
  | i + 1 => fun hi => heapifyFrom (siftFrom v ⟨i, hi⟩) i (Nat.le_of_succ_le hi)


theorem heapifyFrom_correct {α} [TotalOrd α] {n: Nat} {v: Vector α n}:
    {i: Nat} → (hi: i ≤ n) → (∀ j: Fin n, i ≤ j → heap v j) →
    (∀ j: Fin n, heap (heapifyFrom v i hi) j)
  | 0 => fun _ h j => h j (Nat.zero_le j)
  | i + 1 => fun hi h =>
    (heapifyFrom_correct (Nat.le_of_succ_le hi) fun j hj => (
      if a: ancestor i j then
        heap_of_ancestor_heap a (siftFrom_correct (fun s hs =>
          h ⟨child i s, hs⟩ (Nat.succ_le_of_lt lt_child)))
      else
        heap_only_descendants (v₁ := v)
          (fun _ ak => (siftFrom_only_descendants (fun a2 => match two_ancestors ak a2 with
            | .inl a3 => a ((Nat.le_antisymm hj (le_of_ancestor a3)) ▸ ancestor_refl i)
            | .inr a3 => a a3
          )).symm)
          (h j (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hj (fun eq => a (eq ▸ ancestor.refl i)))))
    ))


theorem heapifyFrom_perm {α} [TotalOrd α] {n: Nat} {v: Vector α n}:
    {i: Nat} → (hi: i ≤ n) → v.Perm (heapifyFrom v i hi)
  | 0 => fun _ => Vector.Perm.rfl
  | _ + 1 => fun hi => siftFrom_perm.trans (heapifyFrom_perm (Nat.le_of_succ_le hi))


def heapify {α} [TotalOrd α] {n: Nat} (v: Vector α n): Vector α n :=
  heapifyFrom v n (Nat.le_refl n)


theorem heapify_correct {α} [TotalOrd α] {n: Nat} {v: Vector α n}:
    ∀ j: Fin n, heap (heapify v) j :=
  heapifyFrom_correct (Nat.le_refl n) (fun k hk => False.elim (Nat.not_le_of_lt k.isLt hk))


theorem heapify_perm {α} [TotalOrd α] {n: Nat} {v: Vector α n}:
    v.Perm (heapify v) :=
  heapifyFrom_perm (Nat.le_refl n)


/-
Pop the minimum of the heap
-/
def heapop {α} [TotalOrd α] {n: Nat} (v: Vector α (n + 1)): α × Vector α n :=
  match n with
    | 0 => (v.get 0, #v[])
    | n + 1 =>
      let min := v.get 0
      let last := v.back
      (min, siftFrom (v.pop.set 0 last) 0)


theorem set_self_almostHeap {α} [TotalOrd α] {n: Nat} {v: Vector α n}
  {i: Fin n} {a: α} (h: heap v i):
    almostHeap (v.set i a) i :=
  have h := Eq.mpr (heap.eq_def v i).symm h
  fun s hs => heap_only_descendants (fun _ hj =>
    (Vector.get_set_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt
      (Nat.lt_of_lt_of_le lt_child (le_of_ancestor hj))))).symm
  ) (h s hs).right


theorem heap_pop {α} [TotalOrd α] {n: Nat} {v: Vector α (n + 1)} {i: Fin n}
  (h: heap v i.castSucc):
    heap v.pop i :=
  heap.eq_def v.pop i ▸ fun s hs =>
    have h := (heap.eq_def v i.castSucc ▸ h) s (Nat.lt_of_lt_pred hs)
    ⟨Vector.get_pop ▸ Vector.get_pop (i := ⟨child i s, hs⟩) ▸ h.left,
      heap_pop h.right⟩
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt lt_child


theorem heapop_heap {α} [TotalOrd α]
  {n: Nat} {v: Vector α (n + 2)} (h: heap v 0):
    heap (heapop v).snd 0 :=
  siftFrom_correct (set_self_almostHeap (heap_pop h))


theorem heap_min {α} [t: TotalOrd α] {n: Nat} {v: Vector α n} {i: Fin n} (h: heap v i):
    ∀ j: Fin n, ancestor i j → v.get i ≤ v.get j :=
  fun j hj => match eq_or_child_ancestor_of_ancestor hj with
    | Or.inl eq => (Fin.eq_of_val_eq eq) ▸ (t.le_refl _)
    | Or.inr ⟨s, a⟩ =>
      have h := (heap.eq_def v i ▸ h) s (Nat.lt_of_le_of_lt (le_of_ancestor a) j.isLt)
      t.le_trans h.left (heap_min h.right j a)
  termination_by n - i
  decreasing_by exact Nat.sub_lt_sub_left i.isLt lt_child


theorem heap_min' {α} [TotalOrd α] {n: Nat} {v: Vector α (n + 1)} (h: heap v 0):
    ∀ j: Fin (n + 1), v.get 0 ≤ v.get j :=
  fun j => heap_min h j (zero_ancestor j)


theorem heapop_le {α} [t: TotalOrd α] {n: Nat} {v: Vector α (n + 1)} (h: heap v 0):
    ∀ j: Fin (n + 1), (heapop v).fst ≤ v.get j :=
  match n with
  | 0 => fun j =>
    have eq: j = 0 := Fin.eq_of_val_eq (Nat.lt_one_iff.mp j.isLt)
    eq ▸ t.le_refl (v.get 0)
  | _ + 1 => fun j => heap_min' h j


theorem heapop_mem {α} [TotalOrd α] {n: Nat} {v: Vector α (n + 1)} {a: α}:
    a ∈ v ↔ a = (heapop v).fst ∨ a ∈ (heapop v).snd :=
  match n with
  | 0 => ⟨
      fun mem => Or.inl (
        have ⟨j, eq⟩ := Vector.exists_get_of_mem mem
        have hz: j = 0 := Fin.eq_of_val_eq (Nat.lt_one_iff.mp j.isLt)
        have concl: a = v[0] := hz ▸ eq
        concl
      ),
      fun h => h.resolve_right (Vector.not_mem_empty a) ▸ Vector.get_mem
    ⟩
  | n + 1 => ⟨
      fun mem =>
        have ⟨j, eq⟩ := Vector.exists_get_of_mem mem
        if jz: j = 0 then
          Or.inl (eq.trans (congrArg v.get jz))
        else Or.inr ((Vector.Perm.mem_iff siftFrom_perm).mp (
          if jb: j = n + 1 then
            have hb: (v.pop.set 0 v.back)[0] = v.back := Vector.getElem_set_self _
            have hb2: v.back ∈ v.pop.set 0 v.back := Vector.mem_of_getElem hb
            have beq: v.back = v.get j := Vector.back_eq_getElem.trans (getElem_congr_idx jb.symm)
            (beq.trans eq.symm) ▸ hb2
          else
            have eq1: v.get j = v.pop[j] := (Vector.getElem_pop _).symm
            have eq2: v.pop[j] = (v.pop.set 0 v.back)[j] := (Vector.getElem_set_ne _ _
              (Fin.val_ne_of_ne (Ne.symm jz))).symm
            Vector.mem_of_getElem (eq.trans (eq1.trans eq2)).symm
        ))
      ,
      fun
        | .inl eq => eq ▸ Vector.get_mem
        | .inr mem =>
          have mem2 := (Vector.Perm.mem_iff siftFrom_perm).mpr mem
          match Vector.mem_or_eq_of_mem_set mem2 with
          | .inl mem3 => Vector.mem_of_mem_pop mem3
          | .inr eq => eq ▸ Vector.back_mem
    ⟩

/-
Canonicalize (simultaneously sort and dedup) using heap sort
-/
def reconstructFrom {α} [TotalOrd α] {n: Nat} (hea: Vector α n) (acc: Array α): Array α :=
  match n with
  | 0 => acc
  | _ + 1 =>
    let (min, newhea) := heapop hea
    let newacc := if acc.back? = some min then acc else acc.push min
    reconstructFrom newhea newacc


def reconstructFromInvariant {α}  [TotalOrd α] (acc: Array α): Prop :=
  ∀ i: Nat, ∀ hi: i + 1 < acc.size, acc[i] < acc[i + 1]


theorem reconstructFrom_sorted {α}  [TotalOrd α]
  {n: Nat} {hea: Vector α n} {acc: Array α} (h: ∀ pos: n > 0, heap hea ⟨0, pos⟩)
  (h2: ∀ a b: α, a ∈ acc → b ∈ hea → a ≤ b) (h3: reconstructFromInvariant acc):
    reconstructFromInvariant (reconstructFrom hea acc) := match n with
  | 0 => h3
  | n + 1 =>
    have new_h: ∀ pos: n > 0, heap (heapop hea).snd ⟨0, pos⟩ := fun pos =>
      match n with
      | 0 => False.elim (Nat.not_lt_zero 0 pos)
      | _ + 1 => heapop_heap (h (Nat.zero_lt_succ _))
    have concl: reconstructFromInvariant (reconstructFrom (heapop hea).snd
        (if acc.back? = some (heapop hea).fst then acc else acc.push (heapop hea).fst)) :=
      iteInduction (motive := fun (w: Array α) =>
          reconstructFromInvariant (reconstructFrom (heapop hea).snd w))
        (fun _ => reconstructFrom_sorted new_h (fun a b ha hb =>
          h2 a b ha (heapop_mem.mpr (Or.inr hb))
        ) h3)
        (fun ne => reconstructFrom_sorted new_h (fun a b ha hb =>
          match Array.mem_push.mp ha with
          | .inl mem => h2 a b mem (heapop_mem.mpr (Or.inr hb))
          | .inr eq =>
            have ⟨j, hj⟩ := Vector.get_of_mem (heapop_mem.mpr (Or.inr hb))
            eq ▸ hj ▸ heapop_le (h (Nat.zero_lt_succ _)) j
        ) (fun i hi =>
          have le: i + 1 ≤ acc.size := (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq hi (Array.size_push _)))
          match Nat.lt_or_eq_of_le le with
          | .inl lt => Array.getElem_push_lt lt ▸
            Array.getElem_push_lt (Nat.lt_of_succ_lt lt) ▸ h3 i lt
          | .inr eq =>
            have concl: acc[i] < (acc.push (heapop hea).fst)[i + 1] :=
              getElem_congr_idx eq (coll := Array α) ▸ Array.getElem_push_eq ▸ ⟨
                h2 acc[i] (heapop hea).fst (Array.getElem_mem _) (heapop_mem.mpr (Or.inl rfl)),
                have hidx: i = acc.size - 1 := Nat.add_one_sub_one i ▸ (congrArg (· - 1) eq)
                have hib: acc[i] = acc.back :=
                  (getElem_congr_idx hidx).trans (Array.back_eq_getElem _).symm
                fun eq2 => (Array.back?_eq_back (Nat.lt_of_lt_of_eq (Nat.zero_lt_succ i) eq) ▸ ne)
                  (congrArg some (hib.symm.trans eq2))
              ⟩
            Array.getElem_push_lt (eq ▸ Nat.lt_add_one i) ▸ concl
        ))
    concl


theorem mem_reconstructFrom {α} [TotalOrd α] {n: Nat} {hea: Vector α n} {acc: Array α} {a: α}:
    a ∈ (reconstructFrom hea acc) ↔ a ∈ hea ∨ a ∈ acc :=
  match n with
  | 0 => ⟨
    fun mem => Or.inr mem,
    fun h => have empty: hea = #v[] := Vector.eq_empty_of_size_eq_zero rfl
      h.resolve_left (empty ▸ Vector.not_mem_empty a)
  ⟩
  | _ + 1 => ⟨
    fun mem =>
      have hrec: a ∈ (heapop hea).snd ∨
          a ∈ (if acc.back? = some (heapop hea).fst then acc else acc.push (heapop hea).fst) :=
        (mem_reconstructFrom (hea := (heapop hea).snd)).mp mem
      match hrec with
      | .inl mem2 => Or.inl (heapop_mem.mpr (Or.inr mem2))
      | .inr mem2 => if c: acc.back? = some (heapop hea).fst then
          Or.inr ((congrArg (fun w => a ∈ w) (if_pos c)).mp mem2)
        else
          match Array.mem_or_eq_of_mem_push
            ((congrArg (fun w => a ∈ w) (if_neg c)).mp mem2) with
          | .inl mem3 => Or.inr mem3
          | .inr eq => Or.inl (heapop_mem.mpr (Or.inl eq)),
    fun
    | .inl mem =>
      (mem_reconstructFrom (hea := (heapop hea).snd)).mpr (match heapop_mem.mp mem with
      | .inl eq => Or.inr (
          have concl: a ∈ if acc.back? = some (heapop hea).fst then acc
              else acc.push (heapop hea).fst := iteInduction (motive := fun w => a ∈ w)
            (fun eq2 =>
              have hget: acc[acc.size - 1]? = some a := Array.back?_eq_getElem? ▸ eq ▸ eq2
              Array.mem_of_getElem? hget
            )
            (fun _ => eq ▸ Array.mem_push_self)
          concl
        )
      | .inr mem2 => Or.inl mem2
      )
    | .inr mem =>
      have mem2: a ∈ if acc.back? = some (heapop hea).fst then acc
          else acc.push (heapop hea).fst := iteInduction (motive := fun w => a ∈ w)
        (fun _ => mem) (fun _ => Array.mem_push_of_mem _ mem)
      (mem_reconstructFrom (hea := (heapop hea).snd)).mpr (Or.inr mem2)
  ⟩


def reconstruct {α} [TotalOrd α] {n: Nat} (hea: Vector α n): Array α :=
  reconstructFrom hea #[]


theorem reconstruct_sorted {α} [TotalOrd α] {n: Nat} {hea: Vector α n} (h: ∀ pos: n > 0, heap hea ⟨0, pos⟩):
    reconstructFromInvariant (reconstruct hea) :=
  reconstructFrom_sorted h (fun a _ ha => False.elim (Array.not_mem_empty a ha))
    (fun i hi => False.elim (Nat.not_succ_le_zero i (Nat.le_of_lt hi)))


theorem mem_reconstruct {α} [TotalOrd α] {n: Nat} {hea: Vector α n} {a: α}:
    a ∈ reconstruct hea ↔ a ∈ hea :=
  ⟨
    fun mem => (mem_reconstructFrom.mp mem).resolve_right (Array.not_mem_empty a),
    fun mem => mem_reconstructFrom.mpr (Or.inl mem)
  ⟩


public def canonicalize {α} [TotalOrd α] (v: Array α): Array α :=
  reconstruct (heapify v.toVector)


theorem canonicalize_sorted {α} [TotalOrd α] {v: Array α}:
    reconstructFromInvariant (canonicalize v) :=
  reconstruct_sorted (fun pos => heapify_correct ⟨0, pos⟩)


public theorem mem_canonicalize {α} [TotalOrd α] {v: Array α} {a: α}:
    a ∈ canonicalize v ↔ a ∈ v :=
  mem_reconstruct.trans ((Vector.Perm.mem_iff heapify_perm).symm.trans Vector.mem_mk)


theorem eq_of_sorted_mem {α} [t: TotalOrd α] {v₁ v₂: List α} (h: ∀ a: α, a ∈ v₁ ↔ a ∈ v₂)
  (h1: v₁.Pairwise (· < ·)) (h2: v₂.Pairwise (· < ·)):
    v₁ = v₂ :=
  match v₁ with
  | [] => match v₂ with
    | [] => rfl
    | b::_ => False.elim (List.not_mem_nil ((h b).mpr List.mem_cons_self))
  | a::_ => match v₂ with
    | [] => False.elim (List.not_mem_nil ((h a).mp List.mem_cons_self))
    | b::_ =>
      match List.mem_cons.mp ((h a).mp List.mem_cons_self) with
      | .inl eqb => List.cons_eq_cons.mpr ⟨
        eqb,
        eq_of_sorted_mem (fun c => ⟨
            fun mem => (List.mem_cons.mp ((h c).mp (List.mem_cons_of_mem a mem))).resolve_left
              (eqb ▸ (Ne.symm ((List.pairwise_cons.mp h1).left c mem).right)),
            fun mem => (List.mem_cons.mp ((h c).mpr (List.mem_cons_of_mem b mem))).resolve_left
              (eqb ▸ (Ne.symm ((List.pairwise_cons.mp h2).left c mem).right))
          ⟩)
          (List.pairwise_cons.mp h1).right (List.pairwise_cons.mp h2).right
      ⟩
      | .inr mem =>
        have lt1: b < a := (List.pairwise_cons.mp h2).left a mem
        have lt2: a < b := (List.pairwise_cons.mp h1).left b
          ((List.mem_cons.mp ((h b).mpr List.mem_cons_self)).resolve_left lt1.right)
        False.elim (lt2.right (t.le_antisymm lt2.left lt1.left))


theorem propagate_reconstructFromInvariant {α} [TotalOrd α] {v: Array α}
  {i j: Nat} (hi: i < j) (hj: j < v.size) (h: reconstructFromInvariant v):
    v[i] < v[j] :=
  if eq: i + 1 = j then
    eq ▸ (h i (eq ▸ hj))
  else
    have lt: i + 1 < j := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq
    TotalOrd.lt_trans (h i (Nat.lt_trans lt hj)) (propagate_reconstructFromInvariant lt hj h)


theorem of_reconstructFromInvariant {α} [TotalOrd α] {v: Array α}
  (h: reconstructFromInvariant v):
    v.toList.Pairwise (· < ·) :=
  List.pairwise_iff_getElem.mpr (fun _ _ _ hj hij =>
    propagate_reconstructFromInvariant hij hj h
  )


public theorem canonicalize_correct {α} [TotalOrd α] {v₁ v₂: Array α}:
    canonicalize v₁ = canonicalize v₂ ↔ (∀ a: α, a ∈ v₁ ↔ a ∈ v₂) :=
  ⟨
    fun eq _ => mem_canonicalize.symm.trans (eq ▸ mem_canonicalize),
    fun h => Array.toList_inj.mp (eq_of_sorted_mem
        (fun a => Array.mem_toList_iff.trans ((mem_canonicalize.trans
          ((h a).trans mem_canonicalize.symm)).trans Array.mem_toList_iff.symm))
        (of_reconstructFromInvariant canonicalize_sorted)
        (of_reconstructFromInvariant canonicalize_sorted)
      )
  ⟩
