def List.card {α} [DecidableEq α]: List α → Nat
  | [] => 0
  | h::t => if h ∈ t then t.card else t.card + 1


def List.card_cons_of_mem {α} [DecidableEq α] {a: α} {l: List α} (h: a ∈ l):
    (a::l).card = l.card :=
  ite_cond_eq_true _ _ (eq_true h)


def List.card_cons_of_not_mem {α} [DecidableEq α] {a: α} {l: List α} (h: a ∉ l):
    (a::l).card = l.card + 1 :=
  ite_cond_eq_false _ _ (eq_false h)


theorem List.card_le_length {α} [DecidableEq α]:
    {l: List α} → l.card ≤ l.length
  | [] => Nat.le_refl 0
  | h::t => if mem: h ∈ t then
      (List.card_cons_of_mem mem) ▸ Nat.le_trans List.card_le_length (Nat.le_succ t.length)
    else
       (List.card_cons_of_not_mem mem) ▸ Nat.add_le_add_right List.card_le_length 1


theorem List.card_eq_length_of_nodup {α} [DecidableEq α] {l: List α} (h: l.Nodup):
    l.card = l.length :=
  match l with
  | [] => rfl
  | _::_ => List.card_cons_of_not_mem (List.nodup_cons.mp h).left ▸
    congrArg (· + 1) (List.card_eq_length_of_nodup (List.nodup_cons.mp h).right)


def List.card_filter_of_mem {α} [DecidableEq α]  {a: α} {l: List α} (h: a ∈ l):
    (l.filter (fun x => decide (x ≠ a))).card + 1 = l.card :=
  match l with
  | [] => False.elim (List.not_mem_nil h)
  | b::t =>
    if eq: a = b then
      have filter_eq:
          (b::t).filter (fun x => decide (x ≠ a)) = t.filter (fun x => decide (x ≠ a)) :=
        List.filter_cons_of_neg (fun tr => of_decide_eq_true tr eq.symm)
      if mem: b ∈ t then
        (List.card_cons_of_mem mem) ▸ filter_eq ▸ (List.card_filter_of_mem (eq ▸ mem))
      else
        have f_self: t.filter (fun x => decide (x ≠ a)) = t := List.filter_eq_self.mpr (fun _ hy =>
          decide_eq_true (fun eq2 => mem (eq ▸ eq2 ▸ hy)))
        filter_eq ▸ (List.card_cons_of_not_mem mem) ▸ (congrArg (fun u => u.card + 1) f_self)
    else
      have filter_eq:
          (b::t).filter (fun x => decide (x ≠ a)) = b::(t.filter (fun x => decide (x ≠ a))) :=
        List.filter_cons_of_pos (decide_eq_true (Ne.symm eq))
      have hrec := List.card_filter_of_mem ((List.mem_cons.mp h).resolve_left eq)
      if mem: b ∈ t then
        have mem_filter: b ∈ t.filter (fun x => decide (x ≠ a)) :=
          List.mem_filter.mpr ⟨mem, decide_eq_true (Ne.symm eq)⟩
        (List.card_cons_of_mem mem) ▸ filter_eq ▸ (List.card_cons_of_mem mem_filter) ▸ hrec
      else filter_eq ▸ (List.card_cons_of_not_mem mem) ▸
        (List.card_cons_of_not_mem (fun mem2 => mem (List.mem_filter.mp mem2).left)) ▸
          congrArg (· + 1) hrec


theorem List.card_mono {α} [DecidableEq α] {l₁ l₂: List α} (h: l₁ ⊆ l₂):
    List.card l₁ ≤ List.card l₂ :=
  match l₁ with
  | [] => Nat.zero_le _
  | a::t => if mem: a ∈ t then
      (List.card_cons_of_mem mem) ▸ List.card_mono (List.cons_subset.mp h).right
    else
      let filtered := l₂.filter (fun x => decide (x ≠ a))
      have f_card: filtered.card + 1 = l₂.card := List.card_filter_of_mem
        (List.cons_subset.mp h).left
      have f_sub: t ⊆ filtered := fun _ hy => List.mem_filter.mpr ⟨
          (List.cons_subset.mp h).right hy,
          decide_eq_true (fun eq => mem (eq ▸ hy))
        ⟩
      (List.card_cons_of_not_mem mem) ▸ f_card ▸ Nat.add_le_add_right (List.card_mono f_sub) _


theorem List.card_eq_of_equiv {α} [DecidableEq α] {l₁ l₂: List α} (h: ∀ a, a ∈ l₁ ↔ a ∈ l₂):
    l₁.card = l₂.card :=
  Nat.le_antisymm
    (List.card_mono (fun a ha => (h a).mp ha))
    (List.card_mono (fun a ha => (h a).mpr ha))


theorem List.card_concat {α} [DecidableEq α] {l: List α} {a: α}:
    (l ++ [a]).card = if a ∈ l then l.card else l.card + 1 :=
  (List.card_eq_of_equiv (fun _ => ⟨
    fun hb => (List.mem_append.mp hb).casesOn (List.mem_cons_of_mem a)
      (fun mem => List.mem_singleton.mp mem ▸ List.mem_cons_self),
    fun hb => (List.mem_cons.mp hb).casesOn (fun eq => eq ▸ List.mem_concat_self)
      (fun mem => List.mem_append_left [a] mem),
  ⟩): (l ++ [a]).card = (a::l).card)


theorem List.card_map_inj {α β} [DecidableEq α] [DecidableEq β] (f: α → β)
  (h1: ∀ i j: α, f i = f j → i = j):
    {l: List α} → (l.map f).card = l.card
  | [] => rfl
  | h::_ => ite_congr (propext ⟨
      fun mem => have ⟨i, hi, eq⟩ := List.mem_map.mp mem; (h1 i h eq) ▸ hi,
      fun mem => List.mem_map.mpr ⟨h, mem, rfl⟩
    ⟩)
    (fun _ => List.card_map_inj f h1) (fun _ => congrArg (· + 1) (List.card_map_inj f h1))


def List.rev_range: (n: Nat) → List Nat
  | 0 => []
  | n + 1 => n::(List.rev_range n)


theorem List.mem_rev_range_of_lt {i n: Nat} (h: i < n): i ∈ List.rev_range n :=
  match n with
  | 0 => False.elim (Nat.not_lt_zero i h)
  | n + 1 => if eq: i = n then
      eq ▸ List.mem_cons_self
    else
      List.mem_cons_of_mem _ (List.mem_rev_range_of_lt
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) eq))


theorem List.mem_rev_range_lt {i n: Nat} (h: i ∈ List.rev_range n): i < n :=
  match n with
  | 0 => False.elim (List.not_mem_nil h)
  | n + 1 => if eq: i = n then
      eq ▸ Nat.lt_succ_self n
    else
      Nat.lt_succ_of_lt (List.mem_rev_range_lt ((List.mem_cons.mp h).resolve_left eq))


theorem List.card_rev_range: {n: Nat} → (List.rev_range n).card = n
  | 0 => rfl
  | _ + 1 => (List.card_cons_of_not_mem (fun mem => Nat.ne_of_lt (List.mem_rev_range_lt mem) rfl)) ▸
      congrArg (· + 1) List.card_rev_range


theorem card_at_least {l: List Nat} {n: Nat} (h: ∀ i: Nat, i < n → i ∈ l):
    n ≤ l.card :=
  have sub: List.rev_range n ⊆ l := fun i hi => h i (List.mem_rev_range_lt hi)
  have len: (List.rev_range n).card = n := List.card_rev_range
  len ▸ (List.card_mono sub)


theorem perm_length_at_least {l: List Nat} {n: Nat} (h: ∀ i: Nat, i < n → i ∈ l):
    n ≤ l.length :=
  Nat.le_trans (card_at_least h) List.card_le_length


theorem card_at_most {l: List Nat} {n: Nat} (h: ∀ i: Nat, i ∈ l → i < n):
    l.card ≤ n :=
  have sub: l ⊆ List.rev_range n := fun i hi => List.mem_rev_range_of_lt (h i hi)
  have len: (List.rev_range n).card = n := List.card_rev_range
  len ▸ List.card_mono sub


theorem perm_length_at_most {l: List Nat} {n: Nat} (h1: ∀ i: Nat, i ∈ l → i < n) (h2: l.Nodup):
    l.length ≤ n :=
  List.card_eq_length_of_nodup h2 ▸ (card_at_most h1)


theorem perm_length_eq {l: List Nat} {n: Nat} (h1: ∀ i: Nat, i < n ↔ i ∈ l) (h2: l.Nodup):
    l.length = n :=
  Nat.le_antisymm
    (perm_length_at_most (fun i hi => (h1 i).mpr hi) h2)
    (perm_length_at_least (fun i hi => (h1 i).mp hi))
