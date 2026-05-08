/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

@[expose]
public section
namespace List

def card {α} [DecidableEq α]: List α → Nat
  | [] => 0
  | h::t => if h ∈ t then t.card else t.card + 1


def card_cons_of_mem {α} [DecidableEq α] {a: α} {l: List α} (h: a ∈ l):
    (a::l).card = l.card :=
  ite_cond_eq_true _ _ (eq_true h)


def card_cons_of_not_mem {α} [DecidableEq α] {a: α} {l: List α} (h: a ∉ l):
    (a::l).card = l.card + 1 :=
  ite_cond_eq_false _ _ (eq_false h)


theorem card_le_length {α} [DecidableEq α]:
    {l: List α} → l.card ≤ l.length
  | [] => Nat.le_refl 0
  | h::t => if mem: h ∈ t then
      (card_cons_of_mem mem) ▸ Nat.le_trans card_le_length (Nat.le_succ t.length)
    else
       (card_cons_of_not_mem mem) ▸ Nat.add_le_add_right card_le_length 1


theorem card_eq_length_of_nodup {α} [DecidableEq α] {l: List α} (h: l.Nodup):
    l.card = l.length :=
  match l with
  | [] => rfl
  | _::_ => card_cons_of_not_mem (nodup_cons.mp h).left ▸
    congrArg (· + 1) (card_eq_length_of_nodup (nodup_cons.mp h).right)


theorem card_filter_of_mem {α} [DecidableEq α]  {a: α} {l: List α} (h: a ∈ l):
    (l.filter (fun x => decide (x ≠ a))).card + 1 = l.card :=
  match l with
  | [] => False.elim (not_mem_nil h)
  | b::t =>
    if eq: a = b then
      have filter_eq:
          (b::t).filter (fun x => decide (x ≠ a)) = t.filter (fun x => decide (x ≠ a)) :=
        filter_cons_of_neg (fun tr => of_decide_eq_true tr eq.symm)
      if mem: b ∈ t then
        (card_cons_of_mem mem) ▸ filter_eq ▸ (card_filter_of_mem (eq ▸ mem))
      else
        have f_self: t.filter (fun x => decide (x ≠ a)) = t := filter_eq_self.mpr (fun _ hy =>
          decide_eq_true (fun eq2 => mem (eq ▸ eq2 ▸ hy)))
        filter_eq ▸ (card_cons_of_not_mem mem) ▸ (congrArg (fun u => u.card + 1) f_self)
    else
      have filter_eq:
          (b::t).filter (fun x => decide (x ≠ a)) = b::(t.filter (fun x => decide (x ≠ a))) :=
        filter_cons_of_pos (decide_eq_true (Ne.symm eq))
      have hrec := card_filter_of_mem ((mem_cons.mp h).resolve_left eq)
      if mem: b ∈ t then
        have mem_filter: b ∈ t.filter (fun x => decide (x ≠ a)) :=
          mem_filter.mpr ⟨mem, decide_eq_true (Ne.symm eq)⟩
        (card_cons_of_mem mem) ▸ filter_eq ▸ (card_cons_of_mem mem_filter) ▸ hrec
      else filter_eq ▸ (card_cons_of_not_mem mem) ▸
        (card_cons_of_not_mem (fun mem2 => mem (mem_filter.mp mem2).left)) ▸
          congrArg (· + 1) hrec


theorem card_mono {α} [DecidableEq α] {l₁ l₂: List α} (h: l₁ ⊆ l₂):
    card l₁ ≤ card l₂ :=
  match l₁ with
  | [] => Nat.zero_le _
  | a::t => if mem: a ∈ t then
      (card_cons_of_mem mem) ▸ card_mono (cons_subset.mp h).right
    else
      let filtered := l₂.filter (fun x => decide (x ≠ a))
      have f_card: filtered.card + 1 = l₂.card := card_filter_of_mem
        (cons_subset.mp h).left
      have f_sub: t ⊆ filtered := fun _ hy => mem_filter.mpr ⟨
          (cons_subset.mp h).right hy,
          decide_eq_true (fun eq => mem (eq ▸ hy))
        ⟩
      (card_cons_of_not_mem mem) ▸ f_card ▸ Nat.add_le_add_right (card_mono f_sub) _


theorem card_eq_of_equiv {α} [DecidableEq α] {l₁ l₂: List α} (h: ∀ a, a ∈ l₁ ↔ a ∈ l₂):
    l₁.card = l₂.card :=
  Nat.le_antisymm
    (card_mono (fun a ha => (h a).mp ha))
    (card_mono (fun a ha => (h a).mpr ha))


theorem card_concat {α} [DecidableEq α] {l: List α} {a: α}:
    (l ++ [a]).card = if a ∈ l then l.card else l.card + 1 :=
  (card_eq_of_equiv (fun _ => ⟨
    fun hb => (mem_append.mp hb).casesOn (mem_cons_of_mem a)
      (fun mem => mem_singleton.mp mem ▸ mem_cons_self),
    fun hb => (mem_cons.mp hb).casesOn (fun eq => eq ▸ mem_concat_self)
      (fun mem => mem_append_left [a] mem),
  ⟩): (l ++ [a]).card = (a::l).card)


theorem card_map_inj {α β} [DecidableEq α] [DecidableEq β] (f: α → β)
  (h1: ∀ i j: α, f i = f j → i = j):
    {l: List α} → (l.map f).card = l.card
  | [] => rfl
  | h::_ => ite_congr (propext ⟨
      fun mem => have ⟨i, hi, eq⟩ := mem_map.mp mem; (h1 i h eq) ▸ hi,
      fun mem => mem_map.mpr ⟨h, mem, rfl⟩
    ⟩)
    (fun _ => card_map_inj f h1) (fun _ => congrArg (· + 1) (card_map_inj f h1))


def rev_range: (n: Nat) → List Nat
  | 0 => []
  | n + 1 => n::(rev_range n)


theorem mem_rev_range_of_lt {i n: Nat} (h: i < n): i ∈ rev_range n :=
  match n with
  | 0 => False.elim (Nat.not_lt_zero i h)
  | n + 1 => if eq: i = n then
      eq ▸ mem_cons_self
    else
      mem_cons_of_mem _ (mem_rev_range_of_lt
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) eq))


theorem mem_rev_range_lt {i n: Nat} (h: i ∈ rev_range n): i < n :=
  match n with
  | 0 => False.elim (not_mem_nil h)
  | n + 1 => if eq: i = n then
      eq ▸ Nat.lt_succ_self n
    else
      Nat.lt_succ_of_lt (mem_rev_range_lt ((mem_cons.mp h).resolve_left eq))


theorem card_rev_range: {n: Nat} → (rev_range n).card = n
  | 0 => rfl
  | _ + 1 => (card_cons_of_not_mem (fun mem => Nat.ne_of_lt (mem_rev_range_lt mem) rfl)) ▸
      congrArg (· + 1) card_rev_range


theorem card_at_least {l: List Nat} {n: Nat} (h: ∀ i: Nat, i < n → i ∈ l):
    n ≤ l.card :=
  have sub: rev_range n ⊆ l := fun i hi => h i (mem_rev_range_lt hi)
  have len: (rev_range n).card = n := card_rev_range
  len ▸ (card_mono sub)


theorem perm_length_at_least {l: List Nat} {n: Nat} (h: ∀ i: Nat, i < n → i ∈ l):
    n ≤ l.length :=
  Nat.le_trans (card_at_least h) card_le_length


theorem card_at_most {l: List Nat} {n: Nat} (h: ∀ i: Nat, i ∈ l → i < n):
    l.card ≤ n :=
  have sub: l ⊆ rev_range n := fun i hi => mem_rev_range_of_lt (h i hi)
  have len: (rev_range n).card = n := card_rev_range
  len ▸ card_mono sub


theorem perm_length_at_most {l: List Nat} {n: Nat} (h1: ∀ i: Nat, i ∈ l → i < n) (h2: l.Nodup):
    l.length ≤ n :=
  card_eq_length_of_nodup h2 ▸ (card_at_most h1)


theorem perm_length_eq {l: List Nat} {n: Nat} (h1: ∀ i: Nat, i < n ↔ i ∈ l) (h2: l.Nodup):
    l.length = n :=
  Nat.le_antisymm
    (perm_length_at_most (fun i hi => (h1 i).mpr hi) h2)
    (perm_length_at_least (fun i hi => (h1 i).mp hi))

end List
end
