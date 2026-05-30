/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.CDFA
import Std.Data.HashMap
import AutoKchp.Internal.Util
import AutoKchp.Internal.Counting

/-
Main DFS (the somewhat complex part)
-/
structure DFSState {a: Nat} (r: CDFA a) where
  idx: Std.HashMap r.σ Nat
  del: Array (Vector Nat a)
  fin: Array Bool


def reindexFrom {a: Nat} (r: CDFA a) (p: r.σ) (s: DFSState r):
    Nat → DFSState r × Nat
  | 0 => (s, 0)
  | fuel + 1 => match s.idx[p]? with
    | none => let i := s.del.size
        (
          Fin.foldl a (fun s b =>
            let (s, j) := reindexFrom r (r.δ p b) s fuel
            { s with del := s.del.modify i (fun v => v.set b j) }
          )
          {
            idx := s.idx.insert p i
            del := s.del.push (Vector.replicate a 0)
            fin := s.fin.push (r.f p)
          },
          i
        )
    | some i => (s, i)


theorem reindexFrom_preserves {a: Nat} {r: CDFA a} {p: r.σ} {s: DFSState r}
  {u: r.σ} {i: Nat} (h: s.idx[u]? = some i):
    {fuel: Nat} → (reindexFrom r p s fuel).fst.idx[u]? = some i
  | 0 => h
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
        Fin.foldl_induction (fun (w: DFSState r) _ => w.idx[u]? = some i)
          (have ne: p ≠ u := fun eq2 => Option.some_ne_none i (h.symm.trans (eq2 ▸ eq));
            (Std.HashMap.getElem?_insert_of_ne ne).trans h)
          (fun _ _ hrec => reindexFrom_preserves hrec)
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


theorem reindexFrom_preserves2 {a: Nat} {r: CDFA a} {p: r.σ} {s: DFSState r}
  {i: Nat} {v: Vector Nat a} (h: s.del[i]? = some v):
    {fuel: Nat} → (reindexFrom r p s fuel).fst.del[i]? = some v
  | 0 => h
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
      have ⟨lt, eq⟩ := Array.getElem?_eq_some_iff.mp h;
      Fin.foldl_induction (fun (w: DFSState r) _ => w.del[i]? = some v)
        ((Array.getElem?_push_lt lt).trans (congrArg some eq))
        (fun _ _ hrec =>
          (Array.getElem?_modify.trans (if_neg (Ne.symm (Nat.ne_of_lt lt)))).trans
            (reindexFrom_preserves2 hrec)
        )
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


theorem reindexFrom_preserves3 {a: Nat} {r: CDFA a} {p: r.σ} {s: DFSState r}
  {i: Nat} {v: Bool} (h: s.fin[i]? = some v):
    {fuel: Nat} → (reindexFrom r p s fuel).fst.fin[i]? = some v
  | 0 => h
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
      have ⟨lt, eq⟩ := Array.getElem?_eq_some_iff.mp h;
      Fin.foldl_induction (fun (w: DFSState r) _ => w.fin[i]? = some v)
        ((Array.getElem?_push_lt lt).trans (congrArg some eq))
        (fun _ _ hrec => reindexFrom_preserves3 hrec)
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


theorem reindexFrom_step {a: Nat} {r: CDFA a} {p: r.σ} {s: DFSState r}:
    {fuel: Nat} → fuel > FiniteHashable.cardinal r.σ - s.idx.size →
      (reindexFrom r p s fuel).fst.idx[p]? = some (reindexFrom r p s fuel).snd
  | 0 => fun hf => False.elim (Nat.not_lt_zero _ hf)
  | _ + 1 => match eq: s.idx[p]? with
    | none => fun _ => reindexFrom.eq_def r p s _ ▸ eq ▸
        Fin.foldl_induction (fun (w: DFSState r) _ => w.idx[p]? = some s.del.size)
          Std.HashMap.getElem?_insert_self
          (fun _ _ hrec => reindexFrom_preserves hrec)
    | some _ => fun _ => reindexFrom.eq_def r p s _ ▸ eq ▸ eq


theorem reindexFrom_size {a: Nat} {r: CDFA a} {p: r.σ} {s: DFSState r}:
    {fuel: Nat} → (reindexFrom r p s fuel).fst.idx.size ≥ s.idx.size
  | 0 => Nat.le_refl _
  | _ + 1 => match eq: s.idx[p]? with
    | none => reindexFrom.eq_def r p s _ ▸ eq ▸
        Fin.foldl_induction (fun (w: DFSState r) _ => w.idx.size ≥ s.idx.size)
          Std.HashMap.size_le_size_insert
          (fun _ _ hrec => Nat.le_trans hrec reindexFrom_size)
    | some _ => reindexFrom.eq_def r p s _ ▸ eq ▸ Nat.le_refl _


def invariant {a: Nat} (r: CDFA a) (grey: List r.σ) (s: DFSState r): Prop :=
  s.idx.size = s.del.size ∧ s.idx.size = s.fin.size ∧
  (∀ i: Nat, i < s.idx.size ↔ (∃ p: r.σ, s.idx[p]? = some i)) ∧
  (∀ p: r.σ, p ∉ grey → s.idx[p]?.allP
    (fun i => ∃ hi1: i < s.del.size, ∃ hi2: i < s.fin.size,
      (∀ b: Fin a, s.idx[r.δ p b]? = some (s.del[i].get b)) ∧ r.f p = s.fin[i]))


theorem hashmap_counting_inj {α} [FiniteHashable α] {m: Std.HashMap α Nat}
  (h: ∀ i: Nat, i < m.size ↔ ∃ p: α, m[p]? = some i):
    ∀ p q: α, (hp: p ∈ m) → (hq: q ∈ m) → m[p] = m[q] → p = q :=
  let values := m.toList.map Prod.snd
  have hl: values.length = m.toList.length := List.length_map _
  have hl2: values.length = m.size := hl.trans Std.HashMap.length_toList
  have hv: values.Nodup := List.nodup_of_card_eq_length (Nat.le_antisymm
    (List.card_at_most (fun i hi => have ⟨(p, i2), mem, eq⟩ := List.mem_map.mp hi
      hl2 ▸ ((h i).mpr ⟨p, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (eq ▸ mem)⟩)))
    (List.card_at_least (fun i hi => have ⟨p, hp⟩ := (h i).mp (hl2 ▸ hi)
      List.mem_map.mpr ⟨(p, i), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hp, rfl⟩))
  )
  fun p q hp hq hpq =>
    have memp: (p, m[p]) ∈ m.toList :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr (Std.HashMap.getElem?_eq_some_getElem hp)
    have memq: (q, m[q]) ∈ m.toList :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr (Std.HashMap.getElem?_eq_some_getElem hq)
    have ⟨i, hi, eqi⟩ := List.getElem_of_mem memp
    have ⟨j, hj, eqj⟩ := List.getElem_of_mem memq
    have eqi2: values[i] = m[p] := List.getElem_map _ ▸ congrArg Prod.snd eqi
    have eqj2: values[j] = m[q] := List.getElem_map _ ▸ congrArg Prod.snd eqj
    have eqij: values[i] = values[j] := (eqi2.trans hpq).trans eqj2.symm
    match Nat.lt_trichotomy i j with
      | .inl lt => False.elim (List.pairwise_iff_getElem.mp hv i j _ _ lt eqij)
      | .inr (.inr lt) => False.elim (List.pairwise_iff_getElem.mp hv j i _ _ lt eqij.symm)
      | .inr (.inl eq) => congrArg Prod.fst ((eqi.symm.trans (getElem_congr_idx eq)).trans eqj)


theorem reindexFrom_correct {a: Nat} {r: CDFA a} {p: r.σ}
  {s: DFSState r} (grey: List r.σ) (h: invariant r grey s):
    {fuel: Nat} → fuel > FiniteHashable.cardinal r.σ - s.idx.size →
      invariant r grey (reindexFrom r p s fuel).fst
  | 0 => fun _ => h
  | fuel + 1 => match eq: s.idx[p]? with
    | none => fun hf => reindexFrom.eq_def r p s _ ▸ eq ▸ (
      let motive (s2: DFSState r) (c: Nat): Prop :=
        invariant r (p::grey) s2 ∧
        s2.idx[p]? = some s.del.size ∧
        (∃ hi1: s.del.size < s2.del.size, ∃ hi2: s.del.size < s2.fin.size,
          (∀ b: Fin a, b < c → s2.idx[r.δ p b]? = some (s2.del[s.del.size].get b)) ∧
            r.f p = s2.fin[s.del.size]) ∧
        fuel > FiniteHashable.cardinal r.σ - s2.idx.size
      let sf: DFSState r := (Fin.foldl a (fun s2 b =>
          let (s2, j) := reindexFrom r (r.δ p b) s2 fuel
          { s2 with del := s2.del.modify s.del.size (fun v => v.set b j) }
        )
        {
          idx := s.idx.insert p s.del.size
          del := s.del.push (Vector.replicate a 0)
          fin := s.fin.push (r.f p)
        })
      have ind: motive sf a := Fin.foldl_induction motive
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
                  fun b =>
                    have ne: p ≠ r.δ p2 b :=
                      fun eq2 => Option.some_ne_none _ ((eq2 ▸ (hc b)).symm.trans eq)
                    (Std.HashMap.getElem?_insert_of_ne ne).trans ((hc b).trans
                      (congrArg (fun (w: Vector Nat a) => some (w.get b))
                        (Array.getElem_push_lt hi1).symm)),
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
            Array.getElem_push_eq.symm.trans (getElem_congr_idx hsz),
          ⟩,
          Nat.lt_of_lt_of_le (FiniteHashable.hashmap_insert_remaining_lt
            (fun mem => nomatch (eq ▸ Std.HashMap.isSome_getElem?_iff_mem.mpr mem)))
            (Nat.le_of_lt_succ hf),
        ⟩
        --Induction
        (fun s2 c hrec =>
          have hinv: invariant r (p::grey) (reindexFrom r (r.δ p c) s2 fuel).fst :=
            reindexFrom_correct (p::grey) hrec.left hrec.right.right.right
          ⟨
            ⟨
              Array.size_modify ▸ hinv.left,
              hinv.right.left,
              hinv.right.right.left,
              fun p2 hp2 =>
                let sr := (reindexFrom r (r.δ p c) s2 fuel).fst
                have ne: sr.idx[p2]? ≠ some s.del.size := fun eq2 =>
                  have ⟨mem, eqp⟩ := Std.HashMap.getElem?_eq_some_iff.mp
                    (reindexFrom_preserves hrec.right.left)
                  have ⟨mem2, eqp2⟩ := Std.HashMap.getElem?_eq_some_iff.mp eq2
                  have eq3: p2 = p := hashmap_counting_inj hinv.right.right.left
                    p2 p mem2 mem (eqp2.trans eqp.symm)
                  hp2 (eq3 ▸ List.mem_cons_self)
                have ne2: sr.idx[p2]?.allP (· ≠ s.del.size) := match eq3: sr.idx[p2]? with
                  | some i => (fun eq2 => ne (eq2 ▸ eq3))
                  | none => True.intro
                Option.allP_mp (Option.allP_and.mp ⟨hinv.right.right.right p2 hp2, ne2⟩)
                  (fun i ⟨⟨hi1, hi2, hi3⟩, hi4⟩ => ⟨Array.size_modify ▸ hi1, hi2,
                    ⟨fun b => (hi3.left b).trans (congrArg (fun (w: Vector Nat a) => some (w.get b))
                      (Array.getElem_modify_of_ne (Ne.symm hi4) _ (Array.size_modify ▸ hi1)).symm),
                      hi3.right
                    ⟩
                  ⟩),
            ⟩,
            reindexFrom_preserves (hrec.right.left),
            have ⟨hi1, hi2, hc, hf⟩ := hrec.right.right.left
            have sle: s2.idx.size ≤ (reindexFrom r (r.δ p c) s2 fuel).fst.idx.size :=
              reindexFrom_size
            have sle2: s2.del.size ≤ (reindexFrom r (r.δ p c) s2 fuel).fst.del.size :=
              hrec.left.left ▸ hinv.left ▸ sle
            ⟨
              Nat.lt_of_lt_of_le hi1 (Nat.le_trans sle2 (Nat.le_of_eq Array.size_modify.symm)),
              Nat.lt_of_lt_of_le hi2 (hrec.left.right.left ▸ hinv.right.left ▸ sle),
              fun b hb => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hb) with
                | .inl lt => (reindexFrom_preserves (hc b lt)).trans
                  (congrArg some ((Array.getElem_modify_self _ _).substr
                    (congrArg (fun (w: Vector Nat a) => w.get b) (Option.some_inj.mp
                      (Array.getElem?_eq_getElem _ ▸ reindexFrom_preserves2
                      (Array.getElem?_eq_getElem _)).symm)).trans
                      (Vector.get_set_of_ne (Fin.ne_of_val_ne (Ne.symm (Nat.ne_of_lt lt)))).symm))
                | .inr eq => Eq.substr (Fin.eq_of_val_eq eq)
                  ((reindexFrom_step hrec.right.right.right).trans
                    (congrArg some ((Array.getElem_modify_self
                      (fun (v: Vector Nat a) => v.set c (reindexFrom r (r.δ p c) s2 fuel).snd)
                      (Nat.lt_of_lt_of_le hi1
                        (Nat.le_trans sle2 (Nat.le_of_eq (Eq.symm Array.size_modify))))
                    ).symm ▸ Vector.get_set_self.symm))),
              have c: (reindexFrom r (r.δ p c) s2 fuel).fst.fin[s.del.size]? = some (r.f p) :=
                reindexFrom_preserves3 (Array.getElem?_eq_getElem hi2 ▸ congrArg some hf.symm)
              have ⟨_, c2⟩ := Array.getElem?_eq_some_iff.mp c
              c2.symm,
            ⟩,
            Nat.lt_of_le_of_lt (Nat.sub_le_sub_left reindexFrom_size _) hrec.right.right.right,
          ⟩
        )
      ⟨
        ind.left.left,
        ind.left.right.left,
        ind.left.right.right.left,
        fun p2 hp2 => if eq2: p = p2 then
          have ⟨hi1, hi2, hc, hf⟩ := ind.right.right.left
          (eq2 ▸ ind.right.left) ▸ ⟨hi1, hi2, fun b => eq2 ▸ hc b b.isLt, eq2 ▸ hf⟩
        else
          ind.left.right.right.right p2 (fun mem => match List.mem_cons.mp mem with
            | .inl eq3 => eq2 eq3.symm | .inr mem2 => hp2 mem2),
      ⟩
    )
    | some _ => fun _ => reindexFrom.eq_def r p s _ ▸ eq ▸ h


def reindex {a: Nat} (r: CDFA a): DFSState r × Nat :=
    reindexFrom r r.i { idx := ∅, del := #[], fin := #[] } (FiniteHashable.cardinal r.σ + 1)


def reindexCorrectness {a: Nat} {r: CDFA a} (s: DFSState r): Prop :=
  s.idx.size = s.del.size ∧ s.idx.size = s.fin.size ∧
  (∀ i: Nat, i < s.idx.size ↔ (∃ p: r.σ, s.idx[p]? = some i)) ∧
  (∀ p: r.σ, s.idx[p]?.allP
    (fun i => ∃ hi1: i < s.del.size, ∃ hi2: i < s.fin.size,
      (∀ b: Fin a, s.idx[r.δ p b]? = some (s.del[i].get b)) ∧ r.f p = s.fin[i]))


theorem reindex_correct {a: Nat} {r: CDFA a}:
    reindexCorrectness (reindex r).fst :=
  have concl: invariant r [] (reindex r).fst := reindexFrom_correct []
    ⟨
      Std.HashMap.size_empty, Std.HashMap.size_empty,
      (fun i => ⟨
        fun lt => False.elim (Nat.not_lt_zero i (Std.HashMap.size_empty ▸ lt)),
        fun ⟨_, hp⟩ => nomatch (Std.HashMap.getElem?_empty ▸ hp)
      ⟩),
      fun _ _ => Std.HashMap.getElem?_empty ▸ True.intro
    ⟩
    (Std.HashMap.size_empty ▸ Nat.sub_zero _ ▸ Nat.lt_add_one (FiniteHashable.cardinal r.σ))
  ⟨concl.left, concl.right.left, concl.right.right.left,
    fun p => concl.right.right.right p List.not_mem_nil⟩


theorem reindex_start_correct {a: Nat} {r: CDFA a}:
    (reindex r).fst.idx[r.i]? = some (reindex r).snd :=
  reindexFrom_step (Std.HashMap.size_empty ▸ Nat.sub_zero _ ▸
    Nat.lt_add_one (FiniteHashable.cardinal r.σ))


def constructReindexed {a: Nat} (r: CDFA a): NatCDFA a :=
  let res := reindex r
  let s := res.fst
  have hs: reindexCorrectness s := reindex_correct
  {
    n := s.idx.size,
    i := ⟨res.snd, (hs.right.right.left res.snd).mpr ⟨r.i, reindex_start_correct⟩⟩,
    δ := fun j b => ⟨(s.del[j]'(hs.left ▸ j.isLt)).get b,
      (hs.right.right.left _).mpr (
        have ⟨p, hp⟩ := (hs.right.right.left j).mp j.isLt
        have ⟨_, _, hc, _⟩ := hp ▸ hs.right.right.right p
        ⟨r.δ p b, hc b⟩
      )⟩,
    f := fun j => s.fin[j]'(hs.right.left ▸ j.isLt)
  }


theorem constructReindexed_advance {a: Nat} {r: CDFA a} {l: List (Fin a)}:
    (reindex r).fst.idx[r.advance l]? = some ((constructReindexed r).advance l).val :=
  match List.eq_nil_or_concat l with
  | .inl eq => eq ▸ reindex_start_correct
  | .inr ⟨u, b, eq⟩ =>
    have hrec: (reindex r).fst.idx[r.advance u]? = some ((constructReindexed r).advance u).val :=
      constructReindexed_advance
    have ⟨_, _, hc, _⟩ := hrec ▸ reindex_correct (r := r).right.right.right (r.advance u)
    (List.concat_eq_append ▸ eq) ▸ NatCDFA.advance_concat ▸ CDFA.advance_concat ▸ hc b
  termination_by l.length


theorem constructReindexed_accepts {a: Nat} {r: CDFA a}:
    (constructReindexed r).accepts = r.accepts :=
  funext (fun l =>
    have h := constructReindexed_advance (r := r) (l := l)
    have ⟨_, eq⟩ := Std.HashMap.getElem?_eq_some_iff.mp h
    have ⟨_, _, _, hf⟩ := h ▸ reindex_correct (r := r).right.right.right (r.advance l)
    have hf2: r.accepts l = (reindex r).fst.fin[((constructReindexed r).advance l).val]:= hf
    hf2 ▸ rfl
  )


public section
namespace CDFA

structure ReindexResult {a: Nat} (r: CDFA a) where
  reindexed: NatCDFA a
  correct: reindexed.accepts = r.accepts


def reindex {a: Nat} (r: CDFA a): ReindexResult r := {
  reindexed := constructReindexed r
  correct := constructReindexed_accepts
}

end CDFA

namespace NatCDFA

structure TrimResult {a: Nat} (r: NatCDFA a) where
  trimmed: NatCDFA a
  correct: trimmed.accepts = r.accepts


def trim {a: Nat} (r: NatCDFA a): TrimResult r := {
  trimmed := constructReindexed r.toCDFA
  correct := constructReindexed_accepts.trans
    (funext fun _ => NatCDFA.accepts_toCDFA)
}

end NatCDFA
end
