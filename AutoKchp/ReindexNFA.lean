/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.NFA
import Std.Data.HashMap
import AutoKchp.Internal.Util
import AutoKchp.Internal.Counting


structure DFSState {a: Nat} (r: NFA a) where
  idx: Std.HashMap r.σ Nat
  del: Array (Vector (Array Nat) a)
  fin: Array Bool


def reindexFrom {a: Nat} (r: NFA a) (p: r.σ) (s: DFSState r):
    Nat → DFSState r × Nat
  | 0 => (s, 0)
  | fuel + 1 => match s.idx[p]? with
    | none => let i := s.del.size
        (
          Fin.foldl a (fun s b =>
            (r.δ p b).foldl (
                fun s q =>
                    let (s, j) := reindexFrom r q s fuel
                    { s with del := s.del.modify i (fun v => v.modify b (fun arr => arr.push j))}
            ) s
          )
          {
            idx := s.idx.insert p i
            del := s.del.push (Vector.replicate a #[])
            fin := s.fin.push (r.f p)
          },
          i
        )
    | some i => (s, i)


theorem reindexFrom_preserves {a: Nat} {r: NFA a} {p: r.σ} {s: DFSState r}
  {u: r.σ} {i: Nat} (h: s.idx[u]? = some i):
    {fuel: Nat} → (reindexFrom r p s fuel).fst.idx[u]? = some i
  | 0 => h
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
        Fin.foldl_induction (fun (w: DFSState r) _ => w.idx[u]? = some i)
          (have ne: p ≠ u := fun eq2 => Option.some_ne_none i (h.symm.trans (eq2 ▸ eq));
            (Std.HashMap.getElem?_insert_of_ne ne).trans h)
          (fun _ _ hrec => Array.foldl_induction (fun _ (w: DFSState r) => w.idx[u]? = some i)
            hrec (fun _ _ hrec => reindexFrom_preserves hrec))
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


theorem reindexFrom_preserves2 {a: Nat} {r: NFA a} {p: r.σ} {s: DFSState r}
  {i: Nat} {v: Vector (Array Nat) a} (h: s.del[i]? = some v):
    {fuel: Nat} → (reindexFrom r p s fuel).fst.del[i]? = some v
  | 0 => h
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
      have ⟨lt, eq⟩ := Array.getElem?_eq_some_iff.mp h;
      Fin.foldl_induction (fun (w: DFSState r) _ => w.del[i]? = some v)
        ((Array.getElem?_push_lt lt).trans (congrArg some eq))
        (fun _ _ hrec => Array.foldl_induction (fun _ (w: DFSState r) => w.del[i]? = some v)
            hrec (fun _ _ hrec => (Array.getElem?_modify.trans (if_neg (Ne.symm (Nat.ne_of_lt lt)))).trans
                (reindexFrom_preserves2 hrec))
        )
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


theorem reindexFrom_preserves3 {a: Nat} {r: NFA a} {p: r.σ} {s: DFSState r}
  {i: Nat} {v: Bool} (h: s.fin[i]? = some v):
    {fuel: Nat} → (reindexFrom r p s fuel).fst.fin[i]? = some v
  | 0 => h
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
      have ⟨lt, eq⟩ := Array.getElem?_eq_some_iff.mp h;
      Fin.foldl_induction (fun (w: DFSState r) _ => w.fin[i]? = some v)
        ((Array.getElem?_push_lt lt).trans (congrArg some eq))
        (fun _ _ hrec => Array.foldl_induction (fun _ (w: DFSState r) => w.fin[i]? = some v)
            hrec (fun _ _ hrec => reindexFrom_preserves3 hrec))
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


theorem reindexFrom_step {a: Nat} {r: NFA a} {p: r.σ} {s: DFSState r}:
    {fuel: Nat} → fuel > FiniteHashable.cardinal r.σ - s.idx.size →
      (reindexFrom r p s fuel).fst.idx[p]? = some (reindexFrom r p s fuel).snd
  | 0 => fun hf => False.elim (Nat.not_lt_zero _ hf)
  | _ + 1 => match eq: s.idx[p]? with
    | none => fun _ => reindexFrom.eq_def r p s _ ▸ eq ▸
        Fin.foldl_induction (fun (w: DFSState r) _ => w.idx[p]? = some s.del.size)
          Std.HashMap.getElem?_insert_self
          (fun _ _ hrec => Array.foldl_induction (fun _ (w: DFSState r) => w.idx[p]? = some s.del.size)
            hrec (fun _ _ hrec => reindexFrom_preserves hrec))
    | some _ => fun _ => reindexFrom.eq_def r p s _ ▸ eq ▸ eq


theorem reindexFrom_size {a: Nat} {r: NFA a} {p: r.σ} {s: DFSState r}:
    {fuel: Nat} → (reindexFrom r p s fuel).fst.idx.size ≥ s.idx.size
  | 0 => Nat.le_refl _
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
        Fin.foldl_induction (fun (w: DFSState r) _ => w.idx.size ≥ s.idx.size)
          Std.HashMap.size_le_size_insert
          (fun _ _ hrec => Array.foldl_induction (fun _ (w: DFSState r) => w.idx.size ≥ s.idx.size)
            hrec (fun _ _ hrec => Nat.le_trans hrec reindexFrom_size))
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ Nat.le_refl _


def invariant {a: Nat} (r: NFA a) (grey: List r.σ) (s: DFSState r): Prop :=
  s.idx.size = s.del.size ∧ s.idx.size = s.fin.size ∧
  (∀ i: Nat, i < s.idx.size ↔ (∃ p: r.σ, s.idx[p]? = some i)) ∧
  (∀ p: r.σ, p ∉ grey → s.idx[p]?.allP
    (fun i => ∃ hi1: i < s.del.size, ∃ hi2: i < s.fin.size,
      (∀ b: Fin a, ∃ hs: (s.del[i].get b).size = (r.δ p b).size,
        ∀ k: Nat, (hk: k < (r.δ p b).size) → s.idx[(r.δ p b)[k]]? = some (s.del[i].get b)[k]) ∧
      r.f p = s.fin[i]
    )
  )


def mainMotive {a: Nat} {r: NFA a} (p: r.σ) (grey: List r.σ) (s: DFSState r) (fuel: Nat)
    (s2: DFSState r) (c: Nat): Prop :=
  invariant r (p::grey) s2 ∧
  s2.idx[p]? = some s.del.size ∧
  (∃ hi1: s.del.size < s2.del.size, ∃ hi2: s.del.size < s2.fin.size,
    (∀ b: Fin a, b < c →
      (∃ hs: (s2.del[s.del.size].get b).size = (r.δ p b).size,
        ∀ k: Nat, (hk: k < (r.δ p b).size) → s2.idx[(r.δ p b)[k]]? = some (s2.del[s.del.size].get b)[k])) ∧
    (∀ b: Fin a, b ≥ c → s2.del[s.del.size].get b = #[]) ∧
    r.f p = s2.fin[s.del.size]
  ) ∧
  fuel > FiniteHashable.cardinal r.σ - s2.idx.size


def subMotive {a: Nat} {r: NFA a} (p: r.σ) (grey: List r.σ) (s: DFSState r) (fuel: Nat) (c: Fin a)
    (l: Nat) (s2: DFSState r): Prop :=
  invariant r (p::grey) s2 ∧
  s2.idx[p]? = some s.del.size ∧
  (∃ hi1: s.del.size < s2.del.size, ∃ hi2: s.del.size < s2.fin.size,
    (∀ b: Fin a, b < c → ∃ hs: (s2.del[s.del.size].get b).size = (r.δ p b).size,
      ∀ k: Nat, (hk: k < (r.δ p b).size) → s2.idx[(r.δ p b)[k]]? = some (s2.del[s.del.size].get b)[k]) ∧
    (∃ hs: (s2.del[s.del.size].get c).size = l ∧ l ≤ (r.δ p c).size,
      ∀ k: Nat, (hk: k < l) → s2.idx[(r.δ p c)[k]]? = some (s2.del[s.del.size].get c)[k]) ∧
    (∀ b: Fin a, b ≥ c.val + 1 → s2.del[s.del.size].get b = #[]) ∧
    r.f p = s2.fin[s.del.size]
  ) ∧
  fuel > FiniteHashable.cardinal r.σ - s2.idx.size


def reindexFrom_motive (fuel: Nat): Prop :=
  {a: Nat} → {r: NFA a} → {p: r.σ} → {s: DFSState r} → (grey: List r.σ) →
  invariant r grey s → fuel > FiniteHashable.cardinal r.σ - s.idx.size →
  invariant r grey (reindexFrom r p s fuel).fst


theorem subMotive_step {a: Nat} {r: NFA a} {p: r.σ} {grey: List r.σ} {s: DFSState r} {fuel: Nat}
  {s2: DFSState r} {c: Fin a} {l: Fin (r.δ p c).size} (h: subMotive p grey s fuel c l s2)
  (hfx: reindexFrom_motive fuel):
    subMotive p grey s fuel c l.succ
    {
      (reindexFrom r (r.δ p c)[l] s2 fuel).fst
      with del :=
        (reindexFrom r (r.δ p c)[l] s2 fuel).fst.del.modify s.del.size fun v =>
          v.modify c fun arr => arr.push (reindexFrom r (r.δ p c)[l] s2 fuel).snd
    } :=
  let sr: DFSState r := (reindexFrom r (r.δ p c)[l] s2 fuel).fst
  have hinv: invariant r (p::grey) sr := hfx (p::grey)
    h.left h.right.right.right
  let sr2 := {
    sr with
    del := sr.del.modify s.del.size fun v =>
        v.modify c fun arr => arr.push (reindexFrom r (r.δ p c)[l] s2 fuel).snd,
  }
  have concl: subMotive p grey s fuel c l.succ sr2 := ⟨
    ⟨
      hinv.left.trans Array.size_modify.symm,
      hinv.right.left,
      hinv.right.right.left,
      fun p2 hp2 =>
        have ne: sr.idx[p2]? ≠ some s.del.size := fun eq2 =>
          have ⟨mem, eqp⟩ := Std.HashMap.getElem?_eq_some_iff.mp
            (reindexFrom_preserves h.right.left)
          have ⟨mem2, eqp2⟩ := Std.HashMap.getElem?_eq_some_iff.mp eq2
          have eq3: p2 = p := hashmap_counting_inj hinv.right.right.left
            p2 p mem2 mem (eqp2.trans eqp.symm)
          hp2 (eq3 ▸ List.mem_cons_self)
        have ne2: sr.idx[p2]?.allP (· ≠ s.del.size) := match eq3: sr.idx[p2]? with
          | some i => (fun eq2 => ne (eq2 ▸ eq3))
          | none => True.intro
        Option.allP_mp (Option.allP_and.mp ⟨hinv.right.right.right p2 hp2, ne2⟩)
          (fun i ⟨⟨hi1, hi2, hi3⟩, hi4⟩ =>
            have hi1' := Nat.lt_of_lt_of_eq hi1 Array.size_modify.symm
            ⟨hi1', hi2,
              ⟨fun b => have ⟨hs, hc⟩ := hi3.left b
                ⟨Array.getElem_modify_of_ne (Ne.symm hi4) _ hi1' ▸ hs,
                  fun k hk =>
                    have hck := hc k hk
                    hck.trans (congrArg some (getElem_congr_coll
                      (Array.getElem_modify_of_ne (Ne.symm hi4) _ hi1' ▸ rfl)))
                ⟩,
                hi3.right
              ⟩
            ⟩
          ),
    ⟩,
    reindexFrom_preserves h.right.left,
    have ⟨hi1, hi2, hc, hce, hc2, hf⟩ := h.right.right.left
    have sle: s2.idx.size ≤ sr.idx.size := reindexFrom_size
    have sle2: s2.del.size ≤ sr.del.size := h.left.left ▸ hinv.left ▸ sle
    have hi1' := Nat.lt_of_lt_of_le hi1 (Nat.le_trans sle2 (Nat.le_of_eq Array.size_modify.symm))
    ⟨
      hi1',
      Nat.lt_of_lt_of_le hi2 (h.left.right.left ▸ hinv.right.left ▸ sle),
      fun b hb =>
        have c: sr.del[s.del.size]? = some s2.del[s.del.size] :=
          reindexFrom_preserves2 (Array.getElem?_eq_getElem _)
        have ⟨_, c2⟩ := Array.getElem?_eq_some_iff.mp c
        have ⟨hs, hs2⟩ := hc b hb
        have eq: sr2.del[s.del.size].get b = sr.del[s.del.size].get b :=
          Array.getElem_modify_self _ hi1' ▸
            Vector.get_modify_of_ne (Fin.ne_of_val_ne (Ne.symm (Nat.ne_of_lt hb)))
        have eq2: sr2.del[s.del.size].get b = s2.del[s.del.size].get b := c2 ▸ eq
        ⟨eq2 ▸ hs, fun k hk =>
          reindexFrom_preserves (((hs2 k hk).trans (congrArg some (getElem_congr_coll eq2).symm)))
        ⟩,
      have c1: sr.del[s.del.size]? = some s2.del[s.del.size] :=
        reindexFrom_preserves2 (Array.getElem?_eq_getElem _)
      have ⟨_, c2⟩ := Array.getElem?_eq_some_iff.mp c1
      have eq: sr2.del[s.del.size].get c = (s2.del[s.del.size].get c).push
          (reindexFrom r (r.δ p c)[l] s2 fuel).snd :=
        (congrArg (fun (w: Vector _ a) => w.get c) (Array.getElem_modify_self _ hi1')).trans (
          Vector.get_modify_self.trans (congrArg (fun (w: Vector (Array _) a) => (w.get c).push _) c2))
      have ⟨⟨heq, hle⟩, hh⟩ := hce
      ⟨⟨eq ▸ (heq ▸ Array.size_push _), Nat.succ_le_of_lt l.isLt⟩, fun k hk =>
        (Eq.trans (
          match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
          | .inl lt => reindexFrom_preserves (Array.getElem_push_lt (heq ▸ lt) ▸ hh k lt)
          | .inr eq2 =>
            have eq3: (r.δ p c)[k] = (r.δ p c)[l] := getElem_congr_idx eq2
            Eq.trans (eq3.substr (reindexFrom_step h.right.right.right))
              (congrArg some ((getElem_congr_idx (eq2.trans heq.symm)).trans Array.getElem_push_eq)).symm
        ) (congrArg some (getElem_congr_coll (i := k) eq)).symm)
      ⟩,
      fun b hb =>
        have c: sr.del[s.del.size]? = some s2.del[s.del.size] :=
          reindexFrom_preserves2 (Array.getElem?_eq_getElem _)
        have ⟨_, c2⟩ := Array.getElem?_eq_some_iff.mp c
        Array.getElem_modify_self _ hi1' ▸
          (Vector.get_modify_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_succ_le hb)))).symm ▸
          c2 ▸ (hc2 b hb),
      have c: sr.fin[s.del.size]? = some (r.f p) :=
        reindexFrom_preserves3 (Array.getElem?_eq_getElem hi2 ▸ congrArg some hf.symm)
      have ⟨_, c2⟩ := Array.getElem?_eq_some_iff.mp c
      c2.symm
    ⟩,
    Nat.lt_of_le_of_lt (Nat.sub_le_sub_left reindexFrom_size _) h.right.right.right,
  ⟩
  concl


theorem mainMotive_step {a: Nat} {r: NFA a} {p: r.σ} {grey: List r.σ} {s: DFSState r} {fuel: Nat}
  {s2: DFSState r} {c: Fin a} (h: mainMotive p grey s fuel s2 c)
  (hfx: reindexFrom_motive fuel): mainMotive p grey s fuel
    ((r.δ p c).foldl
      (fun s2 q => {
        (reindexFrom r q s2 fuel).fst
        with del :=
          (reindexFrom r q s2 fuel).fst.del.modify s.del.size fun v =>
            v.modify c fun arr => arr.push (reindexFrom r q s2 fuel).snd
      })
    s2)
    c.val.succ :=
  let sf2: DFSState r := (r.δ p c).foldl
      (fun s2 q => {
        (reindexFrom r q s2 fuel).fst
        with del :=
          (reindexFrom r q s2 fuel).fst.del.modify s.del.size fun v =>
            v.modify c fun arr => arr.push (reindexFrom r q s2 fuel).snd
      })
    s2
  have ind2: subMotive p grey s fuel c (r.δ p c).size sf2 := Array.foldl_induction
    (subMotive p grey s fuel c)
    ⟨
      h.left,
      h.right.left,
      have ⟨hi1, hi2, hc, hc2, hf⟩ := h.right.right.left
      ⟨
        hi1, hi2, hc,
        ⟨⟨Array.size_eq_zero_iff.mpr (hc2 c (Nat.le_refl c)), Nat.zero_le _⟩,
          fun k hk => False.elim (Nat.not_lt_zero k hk)⟩,
        fun b hb => hc2 b (Nat.le_of_succ_le hb),
        hf
      ⟩,
      h.right.right.right,
    ⟩
    (fun l s2 hrec => subMotive_step hrec hfx)
  ⟨
    ind2.left,
    ind2.right.left,
    have ⟨hi1, hi2, hcl, ⟨hs, hce⟩, hcl2, hf⟩ := ind2.right.right.left
    ⟨
      hi1, hi2,
      fun b hb => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hb) with
      | .inl lt => hcl b lt
      | .inr eq => have eq := Fin.eq_of_val_eq eq
        ⟨eq.symm ▸ hs.left, eq.symm ▸ hce⟩,
      hcl2, hf,
    ⟩,
    ind2.right.right.right
  ⟩


theorem reindexFrom_correct {a: Nat} {r: NFA a} {p: r.σ}
  {s: DFSState r} (grey: List r.σ) (h: invariant r grey s):
    {fuel: Nat} → fuel > FiniteHashable.cardinal r.σ - s.idx.size →
      invariant r grey (reindexFrom r p s fuel).fst
  | 0 => fun _ => h
  | fuel + 1 => match eq: s.idx[p]? with
    | none => fun hf =>
      let sf: DFSState r := Fin.foldl a
        (fun s2 b =>
           (r.δ p b).foldl
            (fun s2 q => {
                idx := (reindexFrom r q s2 fuel).fst.idx,
                del :=
                  (reindexFrom r q s2 fuel).fst.del.modify s.del.size fun v =>
                    v.modify b fun arr => arr.push (reindexFrom r q s2 fuel).snd,
                fin := (reindexFrom r q s2 fuel).fst.fin
              }
            ) s2
        )
        {
          idx := s.idx.insert p s.del.size
          del := s.del.push (Vector.replicate a #[])
          fin := s.fin.push (r.f p)
        }
      have concl: invariant r grey sf := (
        have ind: mainMotive p grey s fuel sf a := Fin.foldl_induction (mainMotive p grey s fuel)
          --Initialization
          ⟨
            have hidx: (s.idx.insert p s.del.size).size = s.idx.size + 1 :=
              Std.HashMap.size_insert.trans (dif_neg (Std.HashMap.getElem?_eq_none_iff.mp eq))
            ⟨
              (hidx.trans (congrArg (· + 1) h.left)).trans (Array.size_push _).symm,
              (hidx.trans (congrArg (· + 1) h.right.left)).trans (Array.size_push _).symm,
              fun i =>
                have hi0 := h.right.right.left i
                hidx ▸ ⟨
                  fun hi => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
                    | .inl lt => have ⟨p2, hp2⟩ := hi0.mp lt
                      ⟨p2, (Std.HashMap.getElem?_insert_of_ne (
                        fun eq2 => Option.some_ne_none _ ((eq2 ▸ hp2).symm.trans eq)
                      )).trans hp2⟩
                    | .inr eq2 => ⟨p, (eq2.trans h.left) ▸ Std.HashMap.getElem?_insert_self⟩,
                  fun ⟨p2, hp2⟩ =>
                    if eq2: p = p2 then
                      have is: (s.idx.insert p s.del.size)[p2]? = some s.del.size :=
                        eq2 ▸ Std.HashMap.getElem?_insert_self
                      (Option.some_inj.mp (h.left ▸ is.symm.trans hp2)) ▸ Nat.lt_succ_self s.idx.size
                    else
                      Nat.lt_succ_of_lt (hi0.mpr ⟨p2,
                        (Std.HashMap.getElem?_insert_of_ne eq2).symm.trans hp2⟩),
                ⟩,
              fun p2 nmem =>
                (Std.HashMap.getElem?_insert_of_ne (fun eq2 => nmem (eq2.subst List.mem_cons_self))).symm ▸
                Option.allP_mp (h.right.right.right p2 (mt (List.mem_cons_of_mem p) nmem)) (
                  fun i ⟨hi1, hi2, hc, hf⟩ => ⟨
                    Array.size_push _ ▸ Nat.lt_succ_of_lt hi1,
                    Array.size_push _ ▸ Nat.lt_succ_of_lt hi2,
                    fun b => have ⟨hs, hcb⟩ := hc b
                      ⟨
                        (Array.getElem_push_lt hi1) ▸ hs,
                        fun k hk =>
                          have hck := hcb k hk
                          have ne: p ≠ (r.δ p2 b)[k] :=
                            fun eq2 => Option.some_ne_none _ ((eq2 ▸ hck).symm.trans eq)
                          (Std.HashMap.getElem?_insert_of_ne ne).trans (hck.trans
                            (congrArg some (getElem_congr_coll (congrArg
                              (fun (w: Vector _ a) => w.get b) (Array.getElem_push_lt hi1).symm))))
                      ⟩,
                    hf.trans (Array.getElem_push_lt hi2).symm,
                  ⟩
                )
            ⟩,
            Std.HashMap.getElem?_insert_self,
            have hsz := h.right.left.symm.trans h.left
            ⟨
              Array.size_push _ ▸ Nat.lt_succ_self _,
              hsz ▸ Array.size_push _ ▸ Nat.lt_succ_self _,
              fun b hb => False.elim (Nat.not_lt_zero b hb),
              fun b _ => Array.getElem_push_eq ▸ Vector.get_replicate,
              Array.getElem_push_eq.symm.trans (getElem_congr_idx hsz),
            ⟩,
            Nat.lt_of_lt_of_le (FiniteHashable.hashmap_insert_remaining_lt
              (fun mem => nomatch (eq ▸ Std.HashMap.isSome_getElem?_iff_mem.mpr mem)))
              (Nat.le_of_lt_succ hf),
          ⟩
          --Induction
          (fun s2 c hrec => mainMotive_step hrec (fun grey h1 h2 => reindexFrom_correct grey h1 h2))
        ⟨
          ind.left.left,
          ind.left.right.left,
          ind.left.right.right.left,
          fun p2 hp2 => if eq2: p = p2 then
            have ⟨hi1, hi2, hc, _, hf⟩ := ind.right.right.left
            (eq2 ▸ ind.right.left) ▸ ⟨hi1, hi2, fun b => eq2 ▸ hc b b.isLt, eq2 ▸ hf⟩
          else
            ind.left.right.right.right p2 (fun mem => match List.mem_cons.mp mem with
              | .inl eq3 => eq2 eq3.symm | .inr mem2 => hp2 mem2),
        ⟩
      )
      reindexFrom.eq_def r p s _ ▸ eq ▸ concl
    | some _ => fun _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


def reindex {a: Nat} (r: NFA a): DFSState r × Array Nat :=
  r.i.foldl (fun (s, init) p =>
    let (s, i) := reindexFrom r p s (FiniteHashable.cardinal r.σ + 1)
    (s, init.push i)
  ) ({ idx := ∅, del := #[], fin := #[] }, #[])


def reindexCorrectness {a: Nat} {r: NFA a} (s: DFSState r): Prop :=
  s.idx.size = s.del.size ∧ s.idx.size = s.fin.size ∧
  (∀ i: Nat, i < s.idx.size ↔ (∃ p: r.σ, s.idx[p]? = some i)) ∧
  (∀ p: r.σ, s.idx[p]?.allP
    (fun i => ∃ hi1: i < s.del.size, ∃ hi2: i < s.fin.size,
      (∀ b: Fin a, ∃ hs: (s.del[i].get b).size = (r.δ p b).size,
        ∀ k: Nat, (hk: k < (r.δ p b).size) → s.idx[(r.δ p b)[k]]? = some (s.del[i].get b)[k]) ∧
      r.f p = s.fin[i]
    )
  )


theorem reindex_correct {a: Nat} {r: NFA a}:
    reindexCorrectness (reindex r).fst :=
  have concl: invariant r [] (reindex r).fst := Array.foldl_induction
    (fun _ (w: DFSState r × Array Nat) => invariant r [] w.fst)
    ⟨
      Std.HashMap.size_empty, Std.HashMap.size_empty,
      (fun i => ⟨
        fun lt => False.elim (Nat.not_lt_zero i (Std.HashMap.size_empty ▸ lt)),
        fun ⟨_, hp⟩ => nomatch (Std.HashMap.getElem?_empty ▸ hp)
      ⟩),
      fun _ _ => Std.HashMap.getElem?_empty ▸ True.intro
    ⟩
    (fun _ _ hrec => reindexFrom_correct [] hrec (Nat.lt_succ_of_le (Nat.sub_le _ _)))
  ⟨concl.left, concl.right.left, concl.right.right.left,
    fun p => concl.right.right.right p List.not_mem_nil⟩


theorem reindex_start_correct {a: Nat} {r: NFA a}:
    ∃ hs: (reindex r).snd.size = r.i.size,
    ∀ k: Nat, (hk: k < r.i.size) → (reindex r).fst.idx[r.i[k]]? = some (reindex r).snd[k] :=
  let motive (l: Nat) (res: DFSState r × Array Nat): Prop :=
    ∃ hs: res.snd.size = l ∧ l ≤ r.i.size,
    ∀ k: Nat, (hk: k < l) → res.fst.idx[r.i[k]]? = some res.snd[k]
  have ⟨⟨hs1, _⟩, c⟩: motive r.i.size (reindex r) := Array.foldl_induction motive
    ⟨⟨rfl, Nat.zero_le _⟩, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
    (fun l res ⟨⟨hs1, hs2⟩, hrec⟩ =>
      ⟨⟨hs1 ▸ Array.size_push _, Nat.succ_le_of_lt l.isLt⟩, fun k hk =>
        match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
        | .inl lt => Array.getElem_push_lt (hs1 ▸ lt) ▸ reindexFrom_preserves (hrec k lt)
        | .inr eq =>
          have eq2: r.i[k] = r.i[l] := getElem_congr_idx eq
          Eq.trans (eq2 ▸ reindexFrom_step (Nat.lt_succ_of_le (Nat.sub_le _ _))) (congrArg some
            ((getElem_congr_idx (eq.trans hs1.symm)).trans Array.getElem_push_eq).symm)
      ⟩
    )
  ⟨hs1, c⟩


def constructReindexed {a: Nat} (r: NFA a): NatNFA a :=
  let res := reindex r
  let s := res.fst
  have hs: reindexCorrectness s := reindex_correct
  let del: Array (Vector (Array (Fin s.idx.size)) a) :=
    s.del.pmap (fun v hv => v.pmap (fun v2 hv2 => v2.pmap (fun i hi => ⟨i,
      have ⟨j, hj1, hj2⟩ := Array.getElem_of_mem hv
      have ⟨p, hp⟩ := (hs.right.right.left j).mp (hs.left ▸ hj1)
      have ⟨hj3, hj4, hj5⟩ := hp ▸ hs.right.right.right p
      have ⟨b, hb⟩ := Vector.get_of_mem hv2
      have ⟨k, hk1, hk2⟩ := Array.getElem_of_mem hi
      have ⟨hs2, hj6⟩ := hj5.left b
      have eq := hj2 ▸ hb
      have lt: k < (r.δ p b).size := hs2 ▸ eq ▸ hk1
      (hs.right.right.left i).mpr ⟨(r.δ p b)[k], (hj6 k lt).trans
        (congrArg some ((getElem_congr_coll eq).trans hk2))⟩
    ⟩) (fun _ => id)) (fun _ => id)) (fun _ => id)
  {
    n := s.idx.size,
    i := res.snd.attach.map (fun ⟨i, hi⟩ => ⟨i,
        have ⟨k, hk1, hk2⟩ := Array.getElem_of_mem hi
        have ⟨hss, h⟩ := reindex_start_correct (r := r)
        (hs.right.right.left i).mpr ⟨r.i[k], hk2 ▸ h k (hss ▸ hk1)⟩
      ⟩),
    δ := fun j b => (del[j]'(Nat.lt_of_lt_of_eq (hs.left ▸ j.isLt) Array.size_pmap.symm)).get b,
    f := fun j => s.fin[j]'(hs.right.left ▸ j.isLt)
  }


theorem constructReindex_delta_size {a: Nat} {r: NFA a}
  {i: Fin (reindex r).fst.idx.size} {b: Fin a}:
    ((constructReindexed r).δ i b).size =
      (((reindex r).fst.del[i]'(reindex_correct.left ▸ i.isLt)).get b).size :=
  (congrArg (fun (w: Vector (Array _) a) => (w.get b).size) (Array.getElem_pmap _ _ _)).trans (
    (congrArg Array.size (Vector.get_pmap _)).trans Array.size_pmap)


theorem constructReindexed_delta {a: Nat} {r: NFA a} {i: Fin (reindex r).fst.idx.size}
  {b: Fin a} {k: Nat} (hk: k < ((constructReindexed r).δ i b).size):
    ((constructReindexed r).δ i b)[k].val =
    (((reindex r).fst.del[i]'(reindex_correct.left ▸ i.isLt)).get b)[k]'
      (constructReindex_delta_size ▸ hk) :=
  (congrArg Fin.val (getElem_congr_coll (
    (congrArg (fun (w: Vector _ a) => w.get b) (Array.getElem_pmap _ _ _)).trans
    (Vector.get_pmap _)
  ))).trans ((congrArg Fin.val (Array.getElem_pmap _ _ _)))


theorem constructReindexed_delta' {a: Nat} {r: NFA a} {p q: r.σ} (hp: p ∈ (reindex r).fst.idx) {b: Fin a}:
    q ∈ r.δ p b ↔ ∃ hq: q ∈ (reindex r).fst.idx,
      ⟨(reindex r).fst.idx[q], (reindex_correct.right.right.left _).mpr
        ⟨q, Std.HashMap.getElem?_eq_some_getElem _⟩⟩ ∈ (constructReindexed r).δ
      ⟨(reindex r).fst.idx[p], (reindex_correct.right.right.left _).mpr
        ⟨p, Std.HashMap.getElem?_eq_some_getElem _⟩⟩ b :=
  have eqp := Std.HashMap.getElem?_eq_some_getElem hp
  have ⟨hi1, hi2, hi3, _⟩ := eqp ▸ reindex_correct.right.right.right p
  have ⟨hs, h2⟩ := hi3 b
  let i: Fin (reindex r).fst.idx.size := ⟨(reindex r).fst.idx[p], reindex_correct.left ▸  hi1⟩
  have hs2: ((constructReindexed r).δ i b).size =
    ((reindex r).fst.del[i].get b).size := constructReindex_delta_size
  have hs3 := hs2.trans hs
  ⟨
    fun qmem =>
      have ⟨k, hk1, hk2⟩ := Array.getElem_of_mem qmem
      have hk3: k < ((constructReindexed r).δ i b).size := hs3 ▸ hk1
      have ⟨hq, hq2⟩ := Std.HashMap.getElem?_eq_some_iff.mp (hk2 ▸ h2 k hk1)
      have ddef: (((constructReindexed r).δ i b)[k]'hk3).val = ((reindex r).fst.del[i].get b)[k] :=
        constructReindexed_delta hk3
      have eq := hq2.trans ddef.symm
      have eq2: ((constructReindexed r).δ i b)[k] = ⟨(reindex r).fst.idx[q], _⟩ :=
        Fin.eq_of_val_eq eq.symm
      ⟨hq, Array.mem_of_getElem eq2⟩,
    fun ⟨hq, hq2⟩ =>
      have ⟨k, hk1, hk2⟩ := Array.getElem_of_mem hq2
      have hk3: k < (r.δ p b).size := hs3 ▸ hk1
      have ddef: (((constructReindexed r).δ i b)[k]'hk1).val = ((reindex r).fst.del[i].get b)[k] :=
        constructReindexed_delta hk1
      have eq: ((reindex r).fst.del[i].get b)[k] = (reindex r).fst.idx[q] :=
        ddef.symm.trans (congrArg Fin.val hk2)
      have ⟨hq3, hq4⟩ := Std.HashMap.getElem?_eq_some_iff.mp (eq ▸ h2 k hk3)
      have eq2: (r.δ p b)[k] = q := hashmap_counting_inj reindex_correct.right.right.left
        (r.δ p b)[k] q hq3 hq hq4
      Array.mem_of_getElem eq2
  ⟩


theorem constructReindexed_path {a: Nat} {r: NFA a} {p q: r.σ} (h: p ∈ r.i) {l: List (Fin a)}:
    r.path p q l ↔
    ∃ (hp: p ∈ (reindex r).fst.idx) (hq: q ∈ (reindex r).fst.idx), (constructReindexed r).path
      ⟨(reindex r).fst.idx[p], (reindex_correct.right.right.left _).mpr
        ⟨p, Std.HashMap.getElem?_eq_some_getElem _⟩⟩
      ⟨(reindex r).fst.idx[q], (reindex_correct.right.right.left _).mpr
        ⟨q, Std.HashMap.getElem?_eq_some_getElem _⟩⟩ l :=
  match List.eq_nil_or_concat l with
  | .inl eq =>
    have ⟨k, hk1, hk2⟩ := Array.getElem_of_mem h
    have ⟨hs, h2⟩ := reindex_start_correct (r := r)
    have ⟨hp0, _⟩ := Std.HashMap.getElem?_eq_some_iff.mp (h2 k hk1)
    have hp: p ∈ (reindex r).fst.idx := hk2 ▸ hp0
    eq ▸ ⟨
      fun eq2 => ⟨hp, eq2 ▸ hp, eq2 ▸ rfl⟩,
      fun ⟨hp, hq, eq2⟩ => hashmap_counting_inj reindex_correct.right.right.left
        p q hp hq (Fin.val_eq_of_eq eq2)
    ⟩
  | .inr ⟨s, b, eq⟩ => eq ▸ List.concat_eq_append ▸ NFA.path_concat.trans ⟨
    fun ⟨u, hu1, hu2⟩ =>
      have ⟨hp, hu, h0⟩ := (constructReindexed_path h).mp hu1
      have ⟨hq, hq2⟩ := (constructReindexed_delta' hu).mp hu2
      ⟨hp, hq, NatNFA.path_concat.mpr ⟨⟨(reindex r).fst.idx[u], _⟩, h0, hq2⟩⟩,
    fun ⟨hp, hq, hpq⟩ =>
      have ⟨j, hj1, hj2⟩ := NatNFA.path_concat.mp hpq
      have ⟨u, hu⟩ := (reindex_correct.right.right.left j).mp j.isLt
      have ⟨hu2, hu3⟩ := Std.HashMap.getElem?_eq_some_iff.mp hu
      have eq: j = ⟨(reindex r).fst.idx[u], hu3 ▸ j.isLt⟩ := Fin.eq_of_val_eq hu3.symm
      have h0 := (constructReindexed_path h).mpr ⟨hp, hu2, eq ▸ hj1⟩
      ⟨u, h0, (constructReindexed_delta' hu2).mpr ⟨hq, eq ▸ hj2⟩⟩,
  ⟩
  termination_by l.length


theorem constructReindexed_initial {a: Nat} {r: NFA a} {p: r.σ}:
    p ∈ r.i ↔ ∃ hp: p ∈ (reindex r).fst.idx,
      ⟨(reindex r).fst.idx[p], (reindex_correct.right.right.left _).mpr
        ⟨p, Std.HashMap.getElem?_eq_some_getElem _⟩⟩ ∈ (constructReindexed r).i :=
  have ⟨hs, hs2⟩ := reindex_start_correct (r := r)
  have hs3: (constructReindexed r).i.size = r.i.size :=
    Array.size_map.trans (Array.size_attach.trans hs)
  ⟨
    fun mem =>
      have ⟨k, hk1, hk2⟩ := Array.getElem_of_mem mem
      have ⟨hp, hp2⟩ := Std.HashMap.getElem?_eq_some_iff.mp (hk2 ▸ hs2 k hk1)
      ⟨hp, Array.mem_map.mpr ⟨⟨(reindex r).fst.idx[p], hp2 ▸ Array.getElem_mem _⟩,
        Array.mem_attach _ _, rfl⟩⟩,
    fun ⟨hp, mem⟩ =>
      have ⟨k, hk1, hk2⟩ := Array.getElem_of_mem mem
      have ⟨hp2, hp3⟩ := Std.HashMap.getElem?_eq_some_iff.mp (hs2 k (hs3 ▸ hk1))
      have eq: (constructReindexed r).i[k].val = (reindex r).snd[k] :=
        (congrArg Fin.val (Array.getElem_map _ _)).trans
        (congrArg Subtype.val (Array.getElem_attach _))
      have eq2 := hk2 ▸ hp3.trans eq.symm
      have eq3 := hashmap_counting_inj reindex_correct.right.right.left r.i[k] p hp2 hp eq2
      Array.mem_of_getElem eq3
  ⟩


theorem constructReindexed_final {a: Nat} {r: NFA a} {p: r.σ} (hp: p ∈ (reindex r).fst.idx):
    r.f p ↔ (constructReindexed r).f ⟨(reindex r).fst.idx[p], (reindex_correct.right.right.left _).mpr
      ⟨p, Std.HashMap.getElem?_eq_some_getElem _⟩⟩ :=
  have hp2 := Std.HashMap.getElem?_eq_some_getElem hp
  have ⟨_, _, _, hf⟩ := hp2 ▸ reindex_correct.right.right.right p
  hf ▸ Iff.refl _


theorem constructReindexed_successfulPath {a: Nat} {r: NFA a} {p q: r.σ} {l: List (Fin a)}:
    r.successfulPath p q l ↔ ∃ (hp: p ∈ (reindex r).fst.idx) (hq: q ∈ (reindex r).fst.idx),
      (constructReindexed r).successfulPath
      ⟨(reindex r).fst.idx[p], (reindex_correct.right.right.left _).mpr
        ⟨p, Std.HashMap.getElem?_eq_some_getElem _⟩⟩
      ⟨(reindex r).fst.idx[q], (reindex_correct.right.right.left _).mpr
        ⟨q, Std.HashMap.getElem?_eq_some_getElem _⟩⟩ l :=
  ⟨
    fun ⟨h, hi, hf⟩ =>
      have ⟨hp, hq, h2⟩ := (constructReindexed_path hi).mp h
      have ⟨_, hi2⟩ := constructReindexed_initial.mp hi
      ⟨hp, hq, h2, hi2, (constructReindexed_final hq).mp hf⟩,
    fun ⟨hp, hq, h, hi, hf⟩ =>
      have hi2 := constructReindexed_initial.mpr ⟨hp, hi⟩
      have h2 := (constructReindexed_path hi2).mpr ⟨hp, hq, h⟩
      ⟨h2, hi2, (constructReindexed_final hq).mpr hf⟩
  ⟩


theorem constructReindexed_accepts {a: Nat} {r: NFA a} {l: List (Fin a)}:
    r.accepts l ↔ (constructReindexed r).accepts l :=
  ⟨
    fun ⟨p, q, h⟩ => have ⟨_, _, h2⟩ := constructReindexed_successfulPath.mp h; ⟨_, _, h2⟩,
    fun ⟨p, q, h⟩ =>
      have ⟨p2, hp2⟩ := (reindex_correct.right.right.left p).mp p.isLt
      have ⟨q2, hq2⟩ := (reindex_correct.right.right.left q).mp q.isLt
      have ⟨hp22, eqp2⟩ := Std.HashMap.getElem?_eq_some_iff.mp hp2
      have ⟨hq22, eqq2⟩ := Std.HashMap.getElem?_eq_some_iff.mp hq2
      have eqp3: p = ⟨(reindex r).fst.idx[p2], _⟩ := Fin.eq_of_val_eq eqp2.symm
      have eqq3: q = ⟨(reindex r).fst.idx[q2], _⟩ := Fin.eq_of_val_eq eqq2.symm
      ⟨p2, q2, constructReindexed_successfulPath.mpr ⟨hp22, hq22, eqp3 ▸ eqq3 ▸ h⟩⟩
  ⟩


theorem constructReindexed_accepts' {a: Nat} {r: NFA a}:
    (constructReindexed r).accepts = r.accepts :=
  funext (fun _ => propext constructReindexed_accepts.symm)


public section
namespace NFA

structure ReindexResult {a: Nat} (r: NFA a) where
  reindexed: NatNFA a
  correct: reindexed.accepts = r.accepts


def reindex {a: Nat} (r: NFA a): ReindexResult r := {
  reindexed := constructReindexed r
  correct := constructReindexed_accepts'
}

end NFA

namespace NatNFA

structure TrimResult {a: Nat} (r: NatNFA a) where
  trimmed: NatNFA a
  correct: trimmed.accepts = r.accepts


def trim {a: Nat} (r: NatNFA a): TrimResult r := {
  trimmed := constructReindexed r.toNFA
  correct := constructReindexed_accepts'.trans
    (funext fun _ => propext NatNFA.accepts_toNFA)
}

end NatNFA
end
