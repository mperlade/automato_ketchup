/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.CDFA
import AutoKchp.Internal.Util
import Std.Data.HashSet


def dfsFrom {a: Nat} (r: CDFA a) (p: r.σ) (l: List (Fin a)) (visited: Std.HashSet r.σ):
    Nat → Except (List (Fin a)) (Std.HashSet r.σ)
  | 0 => Except.error []
  | fuel + 1 =>
    if visited.contains p then Except.ok visited
    else if r.f p then Except.error l.reverse
    else Fin.foldlM a
      (fun acc b => dfsFrom r (r.δ p b) (b::l) acc fuel)
      (visited.insert p)


theorem dfsFrom_preserves_mem {a: Nat} {r: CDFA a} {p: r.σ} {l: List (Fin a)}
  {visited: Std.HashSet r.σ} {i: r.σ} (h: i ∈ visited):
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (fun acc => i ∈ acc)
  | 0 => True.intro
  | _ + 1 => iteInduction (fun _ => h) (fun _ => iteInduction
    (fun _ => True.intro) (fun _ => Fin.foldlM_induction
      (fun (w: Except _ _) _ => w.allP _)
      (Except.pure_def ▸ Std.HashSet.mem_insert.mpr (Or.inr h))
      (fun acc _ hrec => match acc with
        | Except.error _ => True.intro
        | Except.ok _ => dfsFrom_preserves_mem hrec
      )
    ))


theorem dfsFrom_step {a: Nat} {r: CDFA a} {p: r.σ} {l: List (Fin a)}
  {visited: Std.HashSet r.σ}:
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (fun acc => p ∈ acc)
  | 0 => True.intro
  | _ + 1 => iteInduction (fun v => v) (fun _ => iteInduction
    (fun _ => True.intro) (fun _ => Fin.foldlM_induction
      (fun (w: Except _ _) _ => w.allP _)
      (Except.pure_def ▸ Std.HashSet.mem_insert_self)
      (fun acc _ hrec => match acc with
        | Except.error _ => True.intro
        | Except.ok _ => dfsFrom_preserves_mem hrec)
    ))


def okInvariant {a: Nat} (r: CDFA a)
  (grey: List r.σ) (acc: Std.HashSet r.σ): Prop :=
    ∀ p: r.σ, p ∉ grey → p ∈ acc → (¬r.f p ∧ (∀ b: Fin a, r.δ p b ∈ acc))


theorem dfsFrom_ok_correct {a: Nat} {r: CDFA a} {p: r.σ} {l: List (Fin a)}
  {visited: Std.HashSet r.σ} (grey: List r.σ) (h: okInvariant r grey visited):
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (okInvariant r grey)
  | 0 => True.intro
  | fuel + 1 => iteInduction (fun _ => h)
    (fun _ => iteInduction (fun _ => True.intro)
      (fun nf =>
        let motive acc c := acc.allP (fun acc2 =>
          okInvariant r (p::grey) acc2
          ∧ ∀ b: Fin a, b < c →  r.δ p b ∈ acc2
        )
        have ind: motive (Fin.foldlM a
            (fun acc b => dfsFrom r (r.δ p b) (b::l) acc fuel) (visited.insert p)) a :=
          Fin.foldlM_induction motive
            (Except.pure_def ▸ ⟨
              fun p2 hp2 vp2 =>
                have ne: p ≠ p2 := (fun eq => hp2 (eq ▸ List.mem_cons_self))
                have nmem: p2 ∉ grey := (fun mem => hp2 (List.mem_cons_of_mem _ mem))
                have ⟨hl, hr⟩ := h p2 nmem (Std.HashSet.mem_of_mem_insert vp2 (beq_eq_false_iff_ne.mpr ne))
                ⟨
                  hl,
                  fun b => Std.HashSet.mem_insert.mpr (Or.inr (hr b))
                ⟩,
              fun b hb => False.elim (Nat.not_lt_zero b hb)
            ⟩)
            (fun acc _ hrec => match acc with
              | Except.error _ => True.intro
              | Except.ok _ => Except.allP_and.mp ⟨
                dfsFrom_ok_correct (p::grey) hrec.left,
                Except.allP_forall.mp (fun c => Except.allP_imp.mp (fun hc =>
                  match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with
                  | .inl lt => dfsFrom_preserves_mem (hrec.right c lt)
                  | .inr eq => Fin.eq_of_val_eq eq ▸ dfsFrom_step
                ))
              ⟩
            )
        Except.allP_mp ind (fun _ ⟨hacc1, hacc2⟩ p2 hp2 v =>
          if eq: p2 == p then ⟨eq_of_beq eq ▸ nf, fun b => eq_of_beq eq ▸ hacc2 b b.isLt⟩
          else hacc1 p2 (fun mem => hp2 ((List.mem_cons.mp mem).resolve_left (ne_of_beq_false (eq_false_of_ne_true eq)))) v
        )
      ))


theorem dfsFrom_size {a: Nat} {r: CDFA a} {p: r.σ}
  {l: List (Fin a)} {visited: Std.HashSet r.σ}:
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (fun acc => acc.size ≥ visited.size)
  | 0 => True.intro
  | _ + 1 => iteInduction (fun _ => Nat.le_refl _) (fun _ => iteInduction
    (fun _ => True.intro)
    (fun _ => Fin.foldlM_induction
      (fun (acc: Except _ (Std.HashSet r.σ)) _ => acc.allP
        (fun acc2 => acc2.size ≥ visited.size))
      (Except.pure_def ▸ Std.HashSet.size_le_size_insert)
      (fun acc _ hrec => match acc with
        | Except.error _ => True.intro
        | Except.ok _ => Except.allP_mp dfsFrom_size (fun _ h2 => Nat.le_trans hrec h2)
      )
    ))


theorem dfsFrom_err_correct {a: Nat} {r: CDFA a} {p: r.σ} {l: List (Fin a)}
  {visited: Std.HashSet r.σ} (h: p = r.advance l.reverse):
    {fuel: Nat} → fuel > FiniteHashable.cardinal r.σ - visited.size →
      (dfsFrom r p l visited fuel).allEP (fun u => r.accepts u)
  | 0 => fun hf => False.elim (Nat.not_lt_zero _ hf)
  | fuel + 1 => fun hf =>
    iteInduction (fun _ => True.intro) (fun nv => iteInduction
      (fun h2 => have concl: r.f (r.advance l.reverse) = true := h ▸ h2; concl)
      (fun _ => (Fin.foldlM_induction
        (fun (w: Except _ _) _ => w.allEP (fun u => r.accepts u) ∧ w.allP
          (fun acc => fuel > FiniteHashable.cardinal r.σ - acc.size))
        (Except.pure_def ▸ ⟨True.intro,
            Nat.lt_of_lt_of_le (FiniteHashable.hashset_insert_remaining_lt nv) (Nat.le_of_lt_succ hf)
          ⟩)
        (fun acc _ hrec => match acc with
          | Except.error _ => hrec
          | Except.ok _ => ⟨
              dfsFrom_err_correct
                (h ▸ List.reverse_cons ▸ CDFA.advance_concat.symm)
                hrec.right,
              Except.allP_mp dfsFrom_size (fun _ le => Nat.lt_of_le_of_lt
                (Nat.sub_le_sub_left le _) hrec.right)
            ⟩
        )).left
      )
    )


def dfs {a: Nat} (r: CDFA a): Option (List (Fin a)) :=
  match dfsFrom r r.i [] ∅ (FiniteHashable.cardinal r.σ + 1) with
  | Except.error l => some l
  | Except.ok _ => none


theorem dfs_some_correct {a: Nat} {r: CDFA a}: (dfs r).all r.accepts :=
  have concl: (dfsFrom r r.i [] ∅ (FiniteHashable.cardinal r.σ + 1)).allEP (fun u => r.accepts u) :=
    dfsFrom_err_correct (rfl: r.i = r.advance [].reverse) (Std.HashSet.size_empty ▸ Nat.le_refl _)
  match eq: dfsFrom r r.i [] ∅ (FiniteHashable.cardinal r.σ + 1) with
  | Except.ok _ => dfs.eq_def r ▸ eq ▸ rfl
  | Except.error _ => dfs.eq_def r ▸ eq ▸ concl


theorem dfs_none_correct {a: Nat} {r: CDFA a} (h: dfs r = none):
    ∀ l: List (Fin a), r.accepts l = false :=
  match eq: dfsFrom r r.i [] ∅ (FiniteHashable.cardinal r.σ + 1) with
    | Except.ok visited =>
      have h: okInvariant r [] visited := eq.subst (dfsFrom_ok_correct [] (fun _ _ v =>
          False.elim (Std.HashSet.not_mem_empty v)))
      have hs: r.i ∈ visited := eq.subst dfsFrom_step
      let rec propagate (u: List (Fin a)): (r.advance u) ∈ visited :=
        match List.eq_nil_or_concat u with
        | .inl eq2 => eq2 ▸ hs
        | .inr ⟨s, b, eq2⟩ =>
          eq2 ▸ List.concat_eq_append ▸ CDFA.advance_concat ▸
            (h (r.advance s) List.not_mem_nil (propagate s)).right b
        termination_by u.length
      fun l => Bool.not_eq_true _ ▸ (h (r.advance l) List.not_mem_nil (propagate l)).left
    | Except.error _ => nomatch (eq ▸ dfs.eq_def r ▸ h)


public section
namespace CDFA

inductive SearchResult {a: Nat} (r: CDFA a) where
  | word: (l: List (Fin a)) → r.accepts l = true → SearchResult r
  | empty: (∀ l: List (Fin a), r.accepts l = false) → SearchResult r


def search {a: Nat} (r: CDFA a): SearchResult r :=
  match eq: dfs r with
  | some w => SearchResult.word w (
      have concl: Option.all r.accepts (some w) := eq ▸ dfs_some_correct
      concl
    )
  | none => SearchResult.empty (dfs_none_correct eq)

end CDFA
end
