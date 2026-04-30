import Automata.RadixSort

/-
Construction of an array of new indices
-/
def reindexFrom (r: Nat → Bool) (n: Nat) (i: Nat) (acc: Array Nat): Array Nat :=
  if acc.size ≥ n then
    acc
  else if r acc.size then
    reindexFrom r n i (acc.push i)
  else
    reindexFrom r n (i + 1) (acc.push i)


theorem size_reindexFrom {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} (h: acc.size ≤ n):
    (reindexFrom r n i acc).size = n :=
  reindexFrom.eq_def _ _ _ _ ▸ iteInduction (motive := fun w: Array Nat => w.size = n)
    (Nat.le_antisymm h)
    (fun h2 =>
      have size_le: acc.size + 1 ≤ n :=
        Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h (fun eq => h2 (eq ▸ Nat.le_refl n)))
      iteInduction (motive := fun w: Array Nat => w.size = n)
        (fun _ => size_reindexFrom (Array.size_push _ ▸ size_le))
        (fun _ => size_reindexFrom (Array.size_push _ ▸ size_le))
    )


theorem reindexFrom_lt {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} (h: acc.size < n):
    reindexFrom r n i acc = if r acc.size
      then reindexFrom r n i (acc.push i)
      else reindexFrom r n (i + 1) (acc.push i) :=
  reindexFrom.eq_def _ _ _ _ ▸ ite_cond_eq_false _ _ (eq_false (Nat.not_le_of_lt h))


theorem getElem_reindexFrom_lt {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat}
  (h1: acc.size ≤ n) {j: Nat} (h2: j < acc.size):
    (reindexFrom r n i acc)[j]? = some acc[j] :=
  reindexFrom.eq_def _ _ _ _ ▸ iteInduction (motive := fun w => w[j]? = some acc[j])
    (fun _ => (Array.getElem?_eq_some_getElem_iff _ _ h2).mpr True.intro)
    (fun h3 =>
      have size_le: acc.size + 1 ≤ n :=
        Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1 (fun eq => h3 (eq ▸ Nat.le_refl n)))
      have h1_rec: (acc.push i).size ≤ n := Array.size_push _ ▸ size_le
      have h2_rec: j < (acc.push i).size := Array.size_push _ ▸ Nat.lt_succ_of_lt h2
      iteInduction (motive := fun w => w[j]? = some acc[j])
        (fun _ => Array.getElem_push_lt h2 ▸ (getElem_reindexFrom_lt h1_rec h2_rec))
        (fun _ => Array.getElem_push_lt h2 ▸ (getElem_reindexFrom_lt h1_rec h2_rec))
    )


theorem getElem_reindexFrom_self {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} (h: acc.size < n):
    (reindexFrom r n i acc)[acc.size]? = some i :=
  have h1_rec: (acc.push i).size ≤ n := Array.size_push _ ▸ Nat.succ_le_of_lt h
  have h2_rec: acc.size < (acc.push i).size := Array.size_push _ ▸ Nat.lt_succ_self _
  reindexFrom_lt h ▸ iteInduction (motive := fun w => w[acc.size]? = some i)
    (fun _ => Eq.trans (getElem_reindexFrom_lt h1_rec h2_rec) (congrArg some Array.getElem_push_eq))
    (fun _ => Eq.trans (getElem_reindexFrom_lt h1_rec h2_rec) (congrArg some Array.getElem_push_eq))


theorem Option.any_mp {α} {p q: α → Bool} {o: Option α} (h1: o.any p) (h2: ∀ a: α, p a → q a): o.any q :=
  match o with
  | none => False.elim (Bool.false_ne_true h1)
  | some a => h2 a h1


theorem reindexFrom_ge_i {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} {k: Nat}
  (h1: acc.size ≤ k) (h2: k < n):
    (reindexFrom r n i acc)[k]?.any (· ≥ i) :=
  have size_lt: acc.size < n := Nat.lt_of_le_of_lt h1 h2
  if h3: k = acc.size then
    h3 ▸ (getElem_reindexFrom_self size_lt) ▸ Option.any_some ▸ decide_eq_true (Nat.le_refl i)
  else
    have size_le: acc.size + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1 (Ne.symm h3))
    (reindexFrom_lt size_lt) ▸ iteInduction (motive := fun w: Array Nat => w[k]?.any (· ≥ i))
      (fun _ => reindexFrom_ge_i (Array.size_push _ ▸ size_le) h2)
      (fun _ =>
        have hrec: (reindexFrom r n (i + 1) (acc.push i))[k]?.any (. ≥ i + 1) :=
          reindexFrom_ge_i (Array.size_push _ ▸ size_le) h2
        Option.any_mp hrec (fun j hj => decide_eq_true (Nat.le_of_succ_le (of_decide_eq_true hj)))
      )


theorem reindexFrom_mono {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} {j k: Nat}
  (h1: acc.size ≤ j) (h2: j ≤ k) (h3: k < n):
    (reindexFrom r n i acc)[j]? ≤ (reindexFrom r n i acc)[k]? :=
  have size_lt: acc.size < n := Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) h3
  if h4: acc.size = j then
      have concl: (reindexFrom r n i acc)[k]?.any (· ≥ i) := reindexFrom_ge_i (h4 ▸ h2) h3
      have ⟨i', eq, hi'⟩ := (Option.any_eq_true _ _).mp concl
      h4 ▸ (getElem_reindexFrom_self size_lt) ▸ eq ▸ Option.some_le_some.mpr (of_decide_eq_true hi')
  else
    have size_le: (acc.push i).size ≤ j := Array.size_push _ ▸ (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1 h4))
    (reindexFrom_lt size_lt) ▸ if h6: r acc.size then
      (ite_cond_eq_true _ _ (eq_true h6)) ▸ reindexFrom_mono size_le h2 h3
    else
      (ite_cond_eq_false _ _ (eq_false h6)) ▸ reindexFrom_mono size_le h2 h3


theorem reindexFrom_adj {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} {j: Nat}
  (h1: acc.size ≤ j) (h2: j + 1 < n):
    (reindexFrom r n i acc)[j + 1]? ≤ (reindexFrom r n i acc)[j]?.map Nat.succ :=
  have succ_size_lt: acc.size + 1 < n := Nat.lt_of_le_of_lt (Nat.succ_le_succ h1) h2
  have size_push_lt: (acc.push i).size < n := (Array.size_push i) ▸ succ_size_lt
  have size_lt: acc.size < n := Nat.lt_of_succ_lt succ_size_lt
  if h3: acc.size = j then
    have right: (reindexFrom r n i acc)[j]?.map Nat.succ = some (i + 1) :=
      Option.map_eq_some_iff.mpr ⟨i, h3 ▸ getElem_reindexFrom_self size_lt, rfl⟩
    right ▸ reindexFrom_lt size_lt ▸iteInduction (motive := fun w: Array Nat => w[j + 1]? ≤ some (i + 1))
      (fun _ =>
        have left: (reindexFrom r n i (acc.push i))[j + 1]? = some i :=
          h3 ▸ (Array.size_push i) ▸ getElem_reindexFrom_self size_push_lt
        have concl: (reindexFrom r n i (acc.push i))[j + 1]? ≤ some (i + 1) :=
          left ▸ Option.some_le_some.mpr (Nat.le.intro rfl)
        concl
      )
      (fun _ =>
        have left: (reindexFrom r n (i + 1) (acc.push i))[j + 1]? = some (i + 1) :=
          h3 ▸ (Array.size_push i) ▸ getElem_reindexFrom_self size_push_lt
        have concl: (reindexFrom r n (i + 1) (acc.push i))[j + 1]? ≤ some (i + 1) :=
          left ▸ Option.some_le_some.mpr (Nat.le_refl (i + 1))
        concl
      )
  else
    have size_le: (acc.push i).size ≤ j := Array.size_push _ ▸ (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1 h3))
    reindexFrom_lt size_lt ▸
      if h4: r acc.size then (ite_cond_eq_true _ _ (eq_true h4) ▸ reindexFrom_adj size_le h2)
      else (ite_cond_eq_false _ _ (eq_false h4) ▸ reindexFrom_adj size_le h2)


theorem getElem_reindexFrom_eq_iff_chain {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} {k: Nat}
  (h1: acc.size ≤ k) (h2: k < n):
    (reindexFrom r n i acc)[k]? = some i ↔ ∀ j: Nat, acc.size ≤ j → j < k → r j :=
  have size_lt: acc.size < n := Nat.lt_of_le_of_lt h1 h2
  if h3: acc.size = k then
    ⟨
      fun _ j hj1 hj2 => False.elim (Nat.not_le_of_lt (h3 ▸ hj2) hj1),
      fun _ => h3 ▸ getElem_reindexFrom_self size_lt
    ⟩
  else
    have size_le: (acc.push i).size ≤ k := Array.size_push _ ▸ (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1 h3))
    reindexFrom_lt size_lt ▸
      iteInduction (motive := fun w: Array Nat => (w[k]? = some i ↔ ∀ j: Nat, acc.size ≤ j → j < k → r j))
      (fun h4 => ⟨
        fun h5 j hj1 hj2 => match Nat.lt_or_eq_of_le hj1 with
          | .inl hj1 => (getElem_reindexFrom_eq_iff_chain size_le h2).mp h5
            j (Array.size_push _ ▸ Nat.succ_le_of_lt hj1) hj2
          | .inr hj1 => hj1 ▸ h4
        ,
        fun h5 => (getElem_reindexFrom_eq_iff_chain size_le h2).mpr
          (fun j hj1 hj2 => h5 j (Nat.le_of_add_right_le (Array.size_push _ ▸ hj1)) hj2)
      ⟩)
      (fun h4 => ⟨
        fun h5 =>
          have ge_i_add_one: (some i).any (· ≥ i + 1) := h5 ▸ (reindexFrom_ge_i size_le h2)
          False.elim (Nat.not_succ_le_self i (of_decide_eq_true ge_i_add_one)),
        fun h5 => False.elim (h4 (h5 acc.size (Nat.le_refl _) (Nat.lt_of_le_of_ne h1 h3))),
      ⟩)


theorem getElem_reindexFrom_eq_iff_chain' {r: Nat → Bool} {n: Nat} {i: Nat} {acc: Array Nat} {k l: Nat}
  (h1: acc.size ≤ k) (h2: k ≤ l) (h3: l < n):
    (reindexFrom r n i acc)[k]? = (reindexFrom r n i acc)[l]? ↔ ∀ j: Nat, k ≤ j → j < l → r j :=
  have size_lt: acc.size < n := Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) h3
  if h4: acc.size = k then
    have concl := getElem_reindexFrom_eq_iff_chain (r := r) (i := i) (h4 ▸ h2) h3
    ⟨
      fun h5 => h4 ▸ concl.mp ((h4 ▸ getElem_reindexFrom_self size_lt) ▸ h5.symm),
      fun h5 => (h4 ▸ getElem_reindexFrom_self size_lt) ▸ (concl.mpr (h4 ▸ h5)).symm
    ⟩
  else
    have size_le: (acc.push i).size ≤ k := Array.size_push _ ▸ (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1 h4))
    (reindexFrom_lt size_lt) ▸ if h6: r acc.size then
      (ite_cond_eq_true _ _ (eq_true h6)) ▸ getElem_reindexFrom_eq_iff_chain' size_le h2 h3
    else
      (ite_cond_eq_false _ _ (eq_false h6)) ▸ getElem_reindexFrom_eq_iff_chain' size_le h2 h3


def reindex (r: Nat → Bool) (n: Nat): Array Nat :=
  reindexFrom r n 0 #[]


theorem size_reindex {r: Nat → Bool} {n: Nat}: (reindex r n).size = n :=
  size_reindexFrom (Nat.zero_le n)


theorem reindex_mono {r: Nat → Bool} {n: Nat} {i j: Nat} (h1: i ≤ j) (h2: j < n):
    (reindex r n)[i]? ≤ (reindex r n)[j]? :=
  reindexFrom_mono (Nat.zero_le i) h1 h2


theorem reindex_adj {r: Nat → Bool} {n: Nat} {i: Nat} (h: i + 1 < n):
    (reindex r n)[i + 1]? ≤ (reindex r n)[i]?.map Nat.succ :=
  reindexFrom_adj (Nat.zero_le i) h


theorem nat_continuity {f: Nat → Nat} (h: ∀ i: Nat, f (i + 1) = f i ∨ f (i + 1) = f i + 1) {j: Nat}:
    {n: Nat} → f 0 ≤ j → j ≤ f n → ∃ k: Nat, k ≤ n ∧ f k = j
  | 0 => fun hj1 hj2 => ⟨0, Nat.le_refl 0, Nat.le_antisymm hj1 hj2⟩
  | n + 1 => fun hj1 hj2 =>
    match h n with
    | .inl is_same =>
      have ⟨k, hk, eq⟩ := nat_continuity h hj1 (is_same ▸ hj2)
      ⟨k, Nat.le_succ_of_le hk, eq⟩
    | .inr is_succ => if eq: j = f (n + 1) then
        ⟨n + 1, Nat.le_refl _, eq.symm⟩
      else
        have j_le: j ≤ f n := Nat.le_of_lt_succ
          (Nat.lt_of_le_of_ne (Nat.le_trans hj2 (Nat.le_of_eq is_succ))
          (fun eq2 => eq (eq2.trans is_succ.symm)))
        have ⟨k, hk, eqk⟩ := nat_continuity h hj1 j_le
        ⟨k, Nat.le_trans hk (Nat.le.intro rfl), eqk⟩


theorem Array.getD_eq_default {α} (v: Array α) (d: α) {n: Nat} (h: v.size ≤ n): v.getD n d = d :=
  dite_cond_eq_false (eq_false (Nat.not_lt_of_le h))


theorem nat_continuty_array {v: Array Nat} (hv: v.size > 0) {j: Nat} (hj1: v[0] ≤ j) (hj2: j ≤ v.back)
  (h: ∀ i: Nat, (hi: i + 1 < v.size) → v[i + 1] = v[i] ∨ v[i + 1] = v[i] + 1):
    j ∈ v :=
  let f (i: Nat) := v.getD i v.back
  have fst: f 0 = v[0] := (Array.getElem_eq_getD v.back).symm
  have lst: f (v.size - 1) = v.back := (Array.getElem_eq_getD v.back).symm
  have ⟨k, hk, eq⟩ := nat_continuity
    (fun i => if hi: i + 1 < v.size then
      (Array.getElem_eq_getD v.back (i := i)) ▸ (Array.getElem_eq_getD v.back (i := i + 1)) ▸ (h i hi)
    else Or.inl (if hi2: i + 1 = v.size then
      have ilt: i < v.size := hi2 ▸ Nat.lt_succ_self i
      (Array.getD_eq_default v v.back (Nat.le_of_eq hi2.symm)).trans
        (Eq.trans (getElem_congr_idx (Nat.pred_eq_of_eq_succ hi2.symm)) (Array.getElem_eq_getD v.back))
    else
      have lei: v.size ≤ i := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hi) (Ne.symm hi2))
      Eq.trans (Array.getD_eq_default v v.back (Nat.le_succ_of_le lei)) (Array.getD_eq_default v v.back lei).symm
    ))
    (fst ▸ hj1) (lst ▸ hj2)
  have sol: j = v[k] := Eq.trans eq.symm (Array.getElem_eq_getD v.back).symm
  sol ▸ Array.getElem_mem (Nat.lt_of_le_pred hv hk)


theorem getElem_reindex_zero {r: Nat → Bool} {n: Nat} (h: n > 0): (reindex r n)[0]'(size_reindex ▸ h) = 0 :=
  Option.some_inj.mp (Array.getElem?_eq_getElem _ ▸ (Eq.trans
    (congrArg _ Array.size_empty.symm) (getElem_reindexFrom_self (Array.size_empty ▸ h))))


theorem reindex_surj {r: Nat → Bool} {n: Nat} (hn: n > 0) {i: Nat}
  (h: i ≤ (reindex r n).back (h := size_reindex ▸ hn)):
    i ∈ reindex r n :=
  nat_continuty_array (size_reindex ▸ hn) ((getElem_reindex_zero hn).symm ▸ Nat.zero_le i) h
    (fun i hi =>
      have le1: (reindex r n)[i] ≤ (reindex r n)[i + 1] :=
        have mono: (reindex r n)[i]? ≤ (reindex r n)[i + 1]? := reindex_mono
          (Nat.le_succ i) (Nat.lt_of_lt_of_eq hi size_reindex)
        Option.some_le_some.mp
          (Array.getElem?_eq_getElem _ (i := i) ▸ Array.getElem?_eq_getElem _ (i := i +1) ▸ mono)
      have le2: (reindex r n)[i + 1] ≤ (reindex r n)[i] + 1 :=
        have adj: (reindex r n)[i + 1]? ≤ (reindex r n)[i]?.map Nat.succ := reindex_adj
          (Nat.lt_of_lt_of_eq hi size_reindex)
        Option.some_le_some.mp (Array.getElem?_eq_getElem _ (i := i +1) ▸ Option.map_some _ (· + 1) ▸
          Array.getElem?_eq_getElem _ (i := i) ▸  adj)
      if same: (reindex r n)[i] = (reindex r n)[i + 1] then
        Or.inl same.symm
      else
        Or.inr (Nat.le_antisymm le2 (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne le1 same)))
    )


theorem getElem_reindex_eq_iff_chain {r: Nat → Bool} {n: Nat} {i j: Nat} (h1: i ≤ j) (h2: j < n):
    (reindex r n)[i]? = (reindex r n)[j]? ↔ ∀ k: Nat, i ≤ k → k < j → r k :=
  getElem_reindexFrom_eq_iff_chain' (Nat.zero_le i) h1 h2

/-
Lemma to (tediously) show that equality in a sorted array is always through a chain
-/
theorem not_lexEq_of_lexLt {radix: Nat → Nat} {f g: (r: Nat) → Fin (radix r)}:
    {s: Nat} → lexLt f g s → ¬lexEq f g s
  | 0 => fun h _ => h
  | s + 1 => fun
    | .inl tail_lt => fun eq => not_lexEq_of_lexLt tail_lt (fun i hi => eq i (Nat.lt_succ_of_lt hi))
    | .inr ⟨_, lt⟩ => fun eq => (Fin.ne_of_val_ne (Nat.ne_of_lt lt)) (eq s (Nat.lt_succ_self s))


theorem not_both_lexLt {radix: Nat → Nat} {f g: (r: Nat) → Fin (radix r)}:
    {s: Nat} → lexLt f g s → lexLt g f s → False
  | 0 => fun _ => id
  | _ + 1 => fun
    | .inl tail_lt1 => fun
      | .inl tail_lt2 => not_both_lexLt tail_lt1 tail_lt2
      | .inr ⟨eq2, _⟩ => not_lexEq_of_lexLt tail_lt1 (fun i hi => (eq2 i hi).symm)
    | .inr ⟨eq1, lt1⟩ => fun
      | .inl tail_lt2 => not_lexEq_of_lexLt tail_lt2 (fun i hi => (eq1 i hi).symm)
      | .inr ⟨_, lt2⟩ => Nat.not_lt_of_lt lt1 lt2


theorem lexLe_antisymm {radix: Nat → Nat} {f g: (r: Nat) → Fin (radix r)} {s: Nat}
  (h1: lexLe f g s) (h2: lexLe g f s):
    lexEq f g s :=
  match h1 with
  | .inl lt1 => h2.casesOn (fun lt2 => False.elim (not_both_lexLt lt1 lt2)) (fun eq i hi => (eq i hi).symm)
  | .inr eq1 => eq1


theorem lexLt_of_lexLt_of_lexEq {radix: Nat → Nat} {e f g: (r: Nat) → Fin (radix r)}:
    {s: Nat} → lexLt e f s → lexEq f g s → lexLt e g s
  | 0 => fun h _ => False.elim h
  | s + 1 => fun
    | .inl tail_lt => fun eq => Or.inl
      (lexLt_of_lexLt_of_lexEq tail_lt (fun i hi => eq i (Nat.lt_succ_of_lt hi)))
    | .inr ⟨eq, lt⟩ => fun eq2 => Or.inr ⟨
        (fun i hi => Eq.trans (eq i hi) (eq2 i (Nat.lt_succ_of_lt hi))),
        Nat.lt_of_lt_of_eq lt (Fin.val_eq_of_eq (eq2 s (Nat.lt_succ_self s)))
      ⟩


theorem lexLt_of_lexEq_of_lexLt {radix: Nat → Nat} {e f g: (r: Nat) → Fin (radix r)}:
    {s: Nat} → lexEq e f s → lexLt f g s → lexLt e g s
  | 0 => fun _ => False.elim
  | s + 1 => fun eq => fun
    | .inl tail_lt => Or.inl
      (lexLt_of_lexEq_of_lexLt (fun i hi => eq i (Nat.lt_succ_of_lt hi)) tail_lt)
    | .inr ⟨eq2, lt⟩ => Or.inr ⟨
      (fun i hi => Eq.trans (eq i (Nat.lt_succ_of_lt hi)) (eq2 i hi)),
      (eq s (Nat.lt_succ_self s)) ▸ lt
    ⟩


theorem lexLt_trans {radix: Nat → Nat} {e f g: (r: Nat) → Fin (radix r)}:
    {s: Nat} → lexLt e f s → lexLt f g s → lexLt e g s
  | 0 => fun _ => False.elim
  | _ + 1 => fun
    | .inl tail_lt1 => fun
      | .inl tail_lt2 => Or.inl (lexLt_trans tail_lt1 tail_lt2)
      | .inr ⟨eq2, _⟩ => Or.inl (lexLt_of_lexLt_of_lexEq tail_lt1 eq2)
    | .inr ⟨eq1, lt1⟩ => fun
      | .inl tail_lt2 => Or.inl (lexLt_of_lexEq_of_lexLt eq1 tail_lt2)
      | .inr ⟨eq2, lt2⟩ => Or.inr ⟨(fun i hi => Eq.trans (eq1 i hi) (eq2 i hi)), Nat.lt_trans lt1 lt2⟩


theorem lexLe_trans {radix: Nat → Nat} {e f g: (r: Nat) → Fin (radix r)} {s: Nat}
  (h1: lexLe e f s) (h2: lexLe f g s): lexLe e g s :=
  match h1 with
  | .inl lt1 => match h2 with
    | .inl lt2 => Or.inl (lexLt_trans lt1 lt2)
    | .inr eq2 => Or.inl (lexLt_of_lexLt_of_lexEq lt1 eq2)
  | .inr eq1 => match h2 with
    | .inl lt2 => Or.inl (lexLt_of_lexEq_of_lexLt eq1 lt2)
    | .inr eq2 => Or.inr (fun i hi => Eq.trans (eq1 i hi) (eq2 i hi))


theorem radixSort_eq_iff_chain {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n: Nat}
  {i j s: Nat} (hi: i < n) (hj: j < n) (h: i ≤ j):
    lexEq
      (f ((radixSort f n s)[i]'(radixSort_size ▸ hi)))
      (f ((radixSort f n s)[j]'(radixSort_size ▸ hj))) s
    ↔ ∀ k: Nat, i ≤ k → (hk2: k < j) → lexEq
      (f ((radixSort f n s)[k]'(radixSort_size ▸ (Nat.lt_trans hk2 hj))))
      (f ((radixSort f n s)[k + 1]'(radixSort_size ▸ (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk2) hj)))) s
  := ⟨
    fun eq k hk1 hk2 =>
      have k_lt: k < n := Nat.lt_trans hk2 hj
      have le1 := radixSort_order' hi k_lt hk1 (s := s) (f := f)
      have le2 := radixSort_order' k_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk2) hj)
        (Nat.le_succ k) (s := s) (f := f)
      have le3 := radixSort_order' (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk2) hj)
        hj (Nat.succ_le_of_lt hk2) (s := s) (f := f)
      have loop := lexLe_trans le3 (lexLe_trans (Or.inr (fun i hi => (eq i hi).symm)) le1)
      lexLe_antisymm le2 loop,
    fun chain =>
      let rec trans_induction (k: Nat) (h1: i ≤ k) (h2: k ≤ j): lexEq
        (f ((radixSort f n s)[i]'(radixSort_size ▸ hi)))
        (f ((radixSort f n s)[k]'(radixSort_size ▸ (Nat.lt_of_le_of_lt h2 hj)))) s :=
        if eq: i = k then
          fun a ha => eq ▸ rfl
        else
          have hk: i < k := Nat.lt_of_le_of_ne h1 eq
          have hrec := trans_induction k.pred (Nat.le_pred_of_lt hk) (Nat.le_trans (Nat.pred_le _) h2)
          have k_lt: k < n := Nat.lt_of_le_of_lt h2 hj
          have succ_pred: k.pred + 1 = k := Nat.succ_pred (Nat.ne_zero_of_lt hk)
          have congr_succ_pred:
              (radixSort f n s)[k.pred + 1]'(radixSort_size ▸ succ_pred ▸ k_lt) =
              (radixSort f n s)[k]'(radixSort_size ▸ k_lt) := getElem_congr_idx succ_pred
          have schain := chain k.pred (Nat.le_pred_of_lt hk)
            (Nat.lt_of_lt_of_le (Nat.pred_lt_self (Nat.zero_lt_of_lt hk)) h2)
          fun a ha =>
            Eq.trans (hrec a ha) (congr_succ_pred ▸ (schain a ha))
      trans_induction j h (Nat.le_refl j)
  ⟩

/-
Composition by the inverse
-/
def composeInvFrom (v w: Array Nat) (h: v.size = w.size) (acc: Array Nat) (i: Nat): Array Nat :=
  if ge: i ≥ w.size then
    acc
  else
    composeInvFrom v w h (acc.setIfInBounds w[i] v[i]) (i + 1)


theorem size_composeInvFrom {v w: Array Nat} {h: v.size = w.size} {acc: Array Nat} {i: Nat}:
    (composeInvFrom v w h acc i).size = acc.size :=
  if ge: i ≥ w.size then
    composeInvFrom.eq_def _ _ _ _ _ ▸ dite_cond_eq_true (eq_true ge) ▸ rfl
  else
    composeInvFrom.eq_def _ _ _ _ _  ▸
      dite_cond_eq_false (eq_false ge) ▸ Eq.trans size_composeInvFrom Array.size_setIfInBounds


theorem composeInvFrom_preserves {v w: Array Nat} {h: v.size = w.size} {acc: Array Nat} {i j: Nat}
  (hi: i < acc.size) (h2: ∀ k: Nat, j ≤ k → (hk: k < w.size) → w[k] ≠ i):
    (composeInvFrom v w h acc j)[i]'(size_composeInvFrom.symm ▸ hi) = acc[i] :=
  if ge: j ≥ w.size then
    getElem_congr_coll (composeInvFrom.eq_def _ _ _ _ _ ▸ (dite_cond_eq_true (eq_true ge)))
  else
    have eq: composeInvFrom v w h acc j = composeInvFrom v w h (acc.setIfInBounds w[j] v[j]) (j + 1) :=
        composeInvFrom.eq_def _ _ _ _ _ ▸ (dite_cond_eq_false (eq_false ge))
    have preserves: (acc.setIfInBounds w[j] v[j])[i]'(Array.size_setIfInBounds ▸ hi) = acc[i] :=
      Array.getElem_setIfInBounds_ne hi (h2 j (Nat.le_refl j) (Nat.lt_of_not_ge ge))
    Eq.trans (Eq.trans
      (getElem_congr_coll eq)
      (composeInvFrom_preserves
        (Array.size_setIfInBounds.symm ▸ hi)
        (fun k hk => h2 k (Nat.le_of_succ_le hk))))
      preserves


theorem composeInvFrom_getElem_self {v w: Array Nat} {h: v.size = w.size} {acc: Array Nat} {i: Nat}
  (hi: i < w.size) (h2: w[i] < acc.size) (h3: w.toList.Nodup):
   (composeInvFrom v w h acc i)[w[i]]'(size_composeInvFrom ▸ h2) = v[i] :=
  have eq: composeInvFrom v w h acc i = composeInvFrom v w h (acc.setIfInBounds w[i] v[i]) (i + 1) :=
      composeInvFrom.eq_def _ _ _ _ _ ▸ (dite_cond_eq_false (eq_false (Nat.not_le_of_lt hi)))
  have intro: (acc.setIfInBounds w[i] v[i])[w[i]]'(Array.size_setIfInBounds ▸ h2) = v[i] :=
    Array.getElem_setIfInBounds_self _
  Eq.trans (Eq.trans
    (getElem_congr_coll eq)
    (composeInvFrom_preserves _ (fun k hk1 hk2 => (Array.getElem_toList hk2) ▸ (Array.getElem_toList hi) ▸
      Ne.symm (List.pairwise_iff_getElem.mp h3 i k hi hk2 (Nat.lt_of_succ_le hk1)))))
    intro


theorem composeInvFrom_getElem_lt {v w: Array Nat} {h: v.size = w.size} {acc: Array Nat} {i j: Nat}
  (hi: i < w.size) (h2: w[i] < acc.size) (h3: w.toList.Nodup) (h4: j ≤ i):
    (composeInvFrom v w h acc j)[w[i]]'(size_composeInvFrom ▸ h2) = v[i] :=
  have not_ge: ¬j ≥ w.size := Nat.not_le_of_lt (Nat.lt_of_le_of_lt h4 hi)
  if eq: j = i then
    eq.symm ▸ (composeInvFrom_getElem_self hi h2 h3)
  else
    have: j < w.size := Nat.lt_of_le_of_lt h4 hi
    have coll_eq: composeInvFrom v w h acc j = composeInvFrom v w h (acc.setIfInBounds w[j] v[j]) (j + 1) :=
      composeInvFrom.eq_def _ _ _ _ _ ▸ (dite_cond_eq_false (eq_false not_ge))
    Eq.trans
      (getElem_congr_coll coll_eq)
      (composeInvFrom_getElem_lt (acc := acc.setIfInBounds w[j] v[j])
        hi (Array.size_setIfInBounds ▸ h2) h3 (Nat.add_one_le_of_lt (Nat.lt_of_le_of_ne h4 eq)))


theorem mem_of_mem_composeInvFrom {v w: Array Nat} {h: v.size = w.size} {acc: Array Nat} {i: Nat}
  {j: Nat} (h2: j ∈ (composeInvFrom v w h acc i)):
    j ∈ acc ∨ j ∈ v :=
  if ge: i ≥ w.size then
    have eq: (composeInvFrom v w h acc i) = acc :=
      composeInvFrom.eq_def _ _ _ _ _ ▸ dite_cond_eq_true (eq_true ge)
    Or.inl (eq ▸ h2)
  else
    have eq: (composeInvFrom v w h acc i) = composeInvFrom v w h (acc.setIfInBounds w[i] v[i]) (i + 1) :=
      composeInvFrom.eq_def _ _ _ _ _ ▸ dite_cond_eq_false (eq_false ge)
    have hrec := mem_of_mem_composeInvFrom (eq ▸ h2)
    match hrec with
    | .inl hrec => match Array.mem_or_eq_of_mem_setIfInBounds hrec with
      | .inl mem_acc => Or.inl mem_acc
      | .inr eq_v => Or.inr (Array.mem_of_getElem eq_v.symm)
    | .inr mem_v => Or.inr mem_v


-- v ∘ w^-1 (w assumed to be a permutation)
def Array.composeInv (v w: Array Nat) (h: v.size = w.size): Array Nat :=
  composeInvFrom v w h (Array.replicate w.size 0) 0


theorem size_composeInv {v w: Array Nat} {h: v.size = w.size}:
    (Array.composeInv v w h).size = w.size :=
  Eq.trans size_composeInvFrom Array.size_replicate


theorem getElem_composeInv {v w: Array Nat} {h: v.size = w.size} {i: Nat}
  (hi: i < w.size) (h2: w[i] < w.size) (h3: w.toList.Nodup):
    (Array.composeInv v w h)[w[i]]'(size_composeInv ▸ h2) = v[i] :=
  composeInvFrom_getElem_lt hi (Array.size_replicate ▸ h2) h3 (Nat.zero_le _)


theorem mem_of_mem_composeInv {v w: Array Nat} {h: v.size = w.size} {i: Nat}
  (h: i ∈ Array.composeInv v w h): i = 0 ∨ i ∈ v :=
  match mem_of_mem_composeInvFrom h with
  | .inl mem_acc => Or.inl (Array.eq_of_mem_replicate mem_acc)
  | .inr mem_v => Or.inr mem_v

/-
Radix dedup algorithm
-/
def bLexEq {radix: Nat → Nat} (f g: (r: Nat) → Fin (radix r)):
    (s: Nat) → Bool
  | 0 => true
  | s + 1 => if f s = g s then bLexEq f g s else false


theorem bLexEq_iff {radix: Nat → Nat} {f g: (r: Nat) → Fin (radix r)}:
    {s: Nat} → bLexEq f g s = true ↔ lexEq f g s
  | 0 => ⟨fun _ i hi => False.elim (Nat.not_lt_zero i hi), fun _ => rfl⟩
  | s + 1 => iteInduction (motive := fun b => b = true ↔ lexEq f g (s + 1))
    (fun eq => ⟨
      fun beq i hi => match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with
        | .inl hi => hi ▸ eq
        | .inr hi => bLexEq_iff.mp beq i hi,
      fun leq => bLexEq_iff.mpr (fun i hi => leq i (Nat.lt_succ_of_lt hi))
    ⟩)
    (fun neq => ⟨
      fun t => False.elim (Bool.false_ne_true t),
      fun leq => False.elim (neq (leq s (Nat.lt_succ_self s))),
    ⟩)


def adjLexEqR {radix: Nat → Nat} (f: Nat → (r: Nat) → Fin (radix r)) (v: Array Nat) (s: Nat):
    Nat → Bool := fun i =>
  if h: i + 1 < v.size then
    bLexEq (f v[i]) (f v[i + 1]) s
  else
    false


theorem adjLexR_iff {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {v: Array Nat} {s i: Nat}
    (h: i + 1 < v.size): adjLexEqR f v s i = true ↔ lexEq (f v[i]) (f v[i + 1]) s :=
  have d: adjLexEqR f v s i = bLexEq (f v[i]) (f v[i + 1]) s := dite_cond_eq_true (eq_true h)
  d ▸ bLexEq_iff


--Returns the new indices, as well as one above the largest
def radixDedup {radix: Nat → Nat} (f: Nat → (r: Nat) → Fin (radix r)) (n s: Nat): Array Nat × Nat :=
  let sort := radixSort f n s
  let reindexed := reindex (adjLexEqR f sort s) n
  (
    Array.composeInv reindexed sort (Eq.trans size_reindex radixSort_size.symm),
    (reindexed.back?.map (· + 1)).getD 0
  )


theorem size_radixDedup {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}:
    (radixDedup f n s).fst.size = n :=
  Eq.trans size_composeInv radixSort_size


--Putting all the pieces together (in a bit of an ugly way)
theorem radixDedup_correct {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat}
  {i j: Nat} (hi: i < n) (hj: j < n):
    (radixDedup f n s).fst[i]'(size_radixDedup ▸ hi) = (radixDedup f n s).fst[j]'(size_radixDedup ▸ hj)
    ↔ lexEq (f i) (f j) s :=
  have ⟨ii, hii, eqii⟩: ∃ ii: Nat, ∃ hii: ii < (radixSort f n s).size, (radixSort f n s)[ii] = i :=
    Array.getElem_of_mem ((radixSort_mem_iff i).mp hi)
  have hii: ii < n := Nat.lt_of_lt_of_eq hii radixSort_size
  have ⟨ij, hij, eqij⟩: ∃ ij: Nat, ∃ hij: ij < (radixSort f n s).size, (radixSort f n s)[ij] = j :=
    Array.getElem_of_mem ((radixSort_mem_iff j).mp hj)
  have hij: ij < n := Nat.lt_of_lt_of_eq hij radixSort_size
  have ci_h: (reindex (adjLexEqR f (radixSort f n s) s) n).size = (radixSort f n s).size :=
      Eq.trans size_reindex radixSort_size.symm
  have get_i:
      ((reindex (adjLexEqR f (radixSort f n s) s) n).composeInv (radixSort f n s) ci_h)[i]'
        (size_composeInv.symm ▸ radixSort_size ▸ hi) =
      (reindex (adjLexEqR f (radixSort f n s) s) n)[ii]'
        (size_reindex ▸ hii) :=
    eqii ▸ getElem_composeInv (radixSort_size ▸ hii) (
      have ineq: (radixSort f n s)[ii] < n :=
        (radixSort_mem_iff (radixSort f n s)[ii]).mpr (Array.getElem_mem _)
      Nat.lt_of_lt_of_eq ineq radixSort_size.symm
    ) radixSort_nodup
  have get_j:
      ((reindex (adjLexEqR f (radixSort f n s) s) n).composeInv (radixSort f n s) ci_h)[j]'
        (size_composeInv.symm ▸ radixSort_size ▸ hj) =
      (reindex (adjLexEqR f (radixSort f n s) s) n)[ij]'
        (size_reindex ▸ hij) :=
    eqij ▸ getElem_composeInv (radixSort_size ▸ hij) (
      have ineq: (radixSort f n s)[ij] < n :=
        (radixSort_mem_iff (radixSort f n s)[ij]).mpr (Array.getElem_mem _)
      Nat.lt_of_lt_of_eq ineq radixSort_size.symm
    ) radixSort_nodup
  have q?: (reindex (adjLexEqR f (radixSort f n s) s) n)[ii] =
      (reindex (adjLexEqR f (radixSort f n s) s) n)[ij]
      ↔ (reindex (adjLexEqR f (radixSort f n s) s) n)[ii]? =
      (reindex (adjLexEqR f (radixSort f n s) s) n)[ij]? :=
    ⟨
      fun eq => Eq.trans (Eq.trans (Array.getElem?_eq_getElem _) (congrArg Option.some eq))
        (Array.getElem?_eq_getElem _).symm,
      fun eq => Option.some_inj.mp (Eq.trans (Eq.trans (Array.getElem?_eq_getElem _).symm eq)
        (Array.getElem?_eq_getElem _))
    ⟩
  get_i ▸ get_j ▸ (Iff.trans q? (if le: ii ≤ ij then
    Iff.trans (getElem_reindex_eq_iff_chain le hij) (eqii ▸ eqij ▸ Iff.trans ⟨
      fun h k hk1 hk2 => (adjLexR_iff
        (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk2) (radixSort_size ▸ hij))).mp (h k hk1 hk2),
      fun h k hk1 hk2 => (adjLexR_iff (
        Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk2) (radixSort_size ▸ hij))).mpr (h k hk1 hk2)
    ⟩ (radixSort_eq_iff_chain hii hij le).symm)
  else
    have le := Nat.le_of_not_ge le
    have leq_symm: lexEq (f i) (f j) s ↔ lexEq (f j) (f i) s := ⟨
      fun h p hp => (h p hp).symm, fun h p hp => (h p hp).symm
    ⟩
    Iff.trans (Iff.trans eq_comm
      (Iff.trans (getElem_reindex_eq_iff_chain le hii) (eqii ▸ eqij ▸ Iff.trans ⟨
        fun h k hk1 hk2 => (adjLexR_iff
          (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk2) (radixSort_size ▸ hii))).mp (h k hk1 hk2),
        fun h k hk1 hk2 => (adjLexR_iff (
          Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk2) (radixSort_size ▸ hii))).mpr (h k hk1 hk2)
      ⟩ (radixSort_eq_iff_chain hij hii le).symm))
    ) leq_symm.symm
  ))


theorem radixDedup_lt {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat} {i: Nat}
  (h: i ∈ (radixDedup f n s).fst): i < (radixDedup f n s).snd :=
  have rdx_size: (radixSort f n s).size = n := radixSort_size
  have nnnz: 0 < n := Nat.lt_of_lt_of_eq (size_composeInv ▸ Array.size_pos_of_mem h) rdx_size
  have idx_valid: n - 1 < (reindex (adjLexEqR f (radixSort f n s) s) n).size :=
    size_reindex ▸ Nat.sub_one_lt (Nat.ne_zero_of_lt nnnz)
  have eq: (reindex (adjLexEqR f (radixSort f n s) s) n).back? =
      some (reindex (adjLexEqR f (radixSort f n s) s) n)[n - 1] :=
    Eq.trans
      Array.back?_eq_getElem?
      (Eq.trans (congrArg _ (congrArg (· - 1) size_reindex)) (Array.getElem?_eq_getElem _))
  have c1: i < (Option.map (fun x => x + 1) (some (reindex (adjLexEqR f (radixSort f n s) s) n)[n - 1])).getD 0 :=
    Option.map_some _ (· + 1) ▸ Option.getD_some ▸ match mem_of_mem_composeInv h with
    | .inl zero => zero ▸ (Nat.zero_lt_succ _)
    | .inr mem =>
      have ⟨j, hj, eqj⟩ := Array.getElem_of_mem mem
      eqj ▸ Nat.lt_succ_of_le (Option.some_le_some.mp (
        Array.getElem?_eq_getElem _ ▸ Array.getElem?_eq_getElem _ ▸ reindex_mono
        (Nat.le_pred_of_lt (Nat.lt_of_lt_of_eq hj size_reindex))
        (Nat.pred_lt_self nnnz)
      ))
  have c2: i < (Option.map (fun x => x + 1) (reindex (adjLexEqR f (radixSort f n s) s) n).back?).getD 0 :=
    eq ▸ c1
  c2


theorem Array.back?_eq_back {α} {v: Array α} (h: 0 < v.size): v.back? = some v.back :=
  getElem?_eq_getElem (Nat.sub_one_lt_of_lt h)


theorem radixDedup_normalized {radix: Nat → Nat} {f: Nat → (r: Nat) → Fin (radix r)} {n s: Nat} {i: Nat}
  (h: i < (radixDedup f n s).snd): i ∈ (radixDedup f n s).fst :=
  have rdx_size: (radixSort f n s).size = n := radixSort_size
  have h: i < (Option.map (fun x => x + 1) (reindex (adjLexEqR f (radixSort f n s) s) n).back?).getD 0 := h
  have nnnz: 0 < n := Nat.zero_lt_of_ne_zero (fun zero =>
    have reindex_empty: reindex (adjLexEqR f (radixSort f n s) s) n = #[] :=
      Array.eq_empty_of_size_eq_zero (size_reindex.trans zero)
    Nat.not_lt_zero i (Nat.lt_of_lt_of_eq (reindex_empty ▸ h)
      (rfl: (Option.map (fun x => x + 1) #[].back?).getD 0 = 0)))
  have h': i < ((some ((reindex (adjLexEqR f (radixSort f n s) s) n).back _)).map (· + 1)).getD 0 :=
    Array.back?_eq_back (Nat.lt_of_lt_of_eq nnnz size_reindex.symm) ▸ h
  have mem: i ∈ reindex (adjLexEqR f (radixSort f n s) s) n := reindex_surj nnnz
    (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq h' rfl))
  have ⟨k, hk, eqk⟩ := Array.getElem_of_mem mem
  have hk': k < (radixSort f n s).size := (size_reindex.trans radixSort_size.symm) ▸ hk
  have cmp := Eq.trans (getElem_composeInv (h := size_reindex.trans radixSort_size.symm)
    (v := (reindex (adjLexEqR f (radixSort f n s) s) n)) hk'
    (radixSort_size ▸ (radixSort_mem_iff (radixSort f n s)[k]).mpr (Array.getElem_mem _))
    radixSort_nodup) eqk
  cmp ▸ Array.getElem_mem _
