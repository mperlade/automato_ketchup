/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.CDFA
import AutoKchp.Internal.Util


def dfsFrom {a: Nat} (r: NatCDFA a) (p: Fin r.n)
  (l: List (Fin a)) (visited: Vector Bool r.n):
    Nat → Except (List (Fin a)) (Vector Bool r.n)
  | 0 => Except.error []
  | fuel + 1 =>
    if visited.get p then Except.ok visited
    else if r.f p then Except.error l.reverse
    else Fin.foldlM a
      (fun acc b => dfsFrom r (r.δ p b) (b::l) acc fuel)
      (visited.set p true)


theorem dfsFrom_preserves_true {a: Nat} {r: NatCDFA a} {p: Fin r.n} {l: List (Fin a)}
  {visited: Vector Bool r.n} {i: Fin r.n} (h: visited.get i = true):
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (fun acc => acc.get i = true)
  | 0 => True.intro
  | _ + 1 => iteInduction (fun _ => h) (fun nv => iteInduction
    (fun _ => True.intro) (fun _ => Fin.foldlM_induction
      (fun (w: Except _ _) _ => w.allP _)
      (have ne2: p ≠ i := fun eq => nv (eq ▸ h);
        Except.pure_def ▸ (Vector.get_set_of_ne ne2).trans h)
      (fun acc _ hrec => match acc with
        | Except.error _ => True.intro
        | Except.ok _ => dfsFrom_preserves_true hrec
      )
    ))


theorem dfsFrom_step {a: Nat} {r: NatCDFA a} {p: Fin r.n} {l: List (Fin a)}
  {visited: Vector Bool r.n}:
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (fun acc => acc.get p = true)
  | 0 => True.intro
  | _ + 1 => iteInduction (fun v => v) (fun _ => iteInduction
    (fun _ => True.intro) (fun _ => Fin.foldlM_induction
      (fun (w: Except _ _) _ => w.allP _)
      (Except.pure_def ▸ Vector.get_set_self)
      (fun acc _ hrec => match acc with
        | Except.error _ => True.intro
        | Except.ok _ => dfsFrom_preserves_true hrec)
    ))


def okInvariant {a: Nat} (r: NatCDFA a)
  (grey: List (Fin r.n)) (acc: Vector Bool r.n): Prop :=
    ∀ p: Fin r.n, p ∉ grey → acc.get p = true → (¬r.f p ∧ (∀ b: Fin a, acc.get (r.δ p b) = true))


theorem dfsFrom_ok_correct {a: Nat} {r: NatCDFA a} {p: Fin r.n} {l: List (Fin a)}
  {visited: Vector Bool r.n} (grey: List (Fin r.n)) (h: okInvariant r grey visited):
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (okInvariant r grey)
  | 0 => True.intro
  | fuel + 1 => iteInduction (fun _ => h)
    (fun nv => iteInduction (fun _ => True.intro)
      (fun nf =>
        let motive acc c := acc.allP (fun acc2 =>
          okInvariant r (p::grey) acc2
          ∧ ∀ b: Fin a, b < c → acc2.get (r.δ p b) = true
        )
        have ind: motive (Fin.foldlM a
            (fun acc b => dfsFrom r (r.δ p b) (b::l) acc fuel) (visited.set p true)) a :=
          Fin.foldlM_induction motive
            (Except.pure_def ▸ ⟨
              fun p2 hp2 vp2 =>
                have ne: p ≠ p2 := (fun eq => hp2 (eq ▸ List.mem_cons_self))
                have nmem: p2 ∉ grey := (fun mem => hp2 (List.mem_cons_of_mem _ mem))
                have ⟨hl, hr⟩ := h p2 nmem ((Vector.get_set_of_ne ne) ▸ vp2)
                ⟨
                  hl,
                  fun b =>
                    have ne2: p ≠ r.δ p2 b := fun eq2 => (nv (eq2 ▸ hr b))
                    (Vector.get_set_of_ne ne2).symm ▸ (hr b)
                ⟩,
              fun b hb => False.elim (Nat.not_lt_zero b hb)
            ⟩)
            (fun acc b hrec => match acc with
              | Except.error _ => True.intro
              | Except.ok acc => Except.allP_and.mp ⟨
                dfsFrom_ok_correct (p::grey) hrec.left,
                Except.allP_forall.mp (fun c => Except.allP_imp.mp (fun hc =>
                  match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with
                  | .inl lt => dfsFrom_preserves_true (hrec.right c lt)
                  | .inr eq => Fin.eq_of_val_eq eq ▸ dfsFrom_step
                ))
              ⟩
            )
        Except.allP_mp ind (fun acc ⟨hacc1, hacc2⟩ p2 hp2 v =>
          if eq: p2 = p then ⟨eq ▸ nf, fun b => eq ▸ hacc2 b b.isLt⟩
          else hacc1 p2 (fun mem => hp2 ((List.mem_cons.mp mem).resolve_left eq)) v
        )
      ))


theorem count_true_set {k: Nat} {v: Vector Bool k} {i: Fin k}
  (h: v.get i = false):
    (v.set i true).count false + 1 = v.count false :=
  have cond1: ((v[i.val] == false) = true) = True := eq_true (Bool.beq_to_eq v[i.val] _ ▸ h)
  have cond2: ((true == false) = true) = False := eq_false (fun eq => nomatch eq)
  have le: v.count false ≥ 1 := Nat.one_le_of_lt (Vector.count_pos_iff.mpr (h ▸ Vector.get_mem))
  (congrArg (· + 1) (Vector.count_set i.isLt)).trans (
    (ite_cond_eq_true 1 0 cond1).symm ▸ (ite_cond_eq_false 1 0 cond2).symm ▸
      Nat.sub_add_cancel le)


theorem dfsFrom_count {a: Nat} {r: NatCDFA a} {p: Fin r.n}
  {l: List (Fin a)} {visited: Vector Bool r.n}:
    {fuel: Nat} → (dfsFrom r p l visited fuel).allP (fun acc => acc.count false ≤ visited.count false)
  | 0 => True.intro
  | _ + 1 => iteInduction (fun _ => Nat.le_refl _) (fun h => iteInduction
    (fun _ => True.intro)
    (fun _ => Fin.foldlM_induction
      (fun (acc: Except _ (Vector Bool r.n)) _ => acc.allP
        (fun acc2 => acc2.count false ≤ visited.count false))
      (Except.pure_def ▸ Nat.le_of_add_le_add_right
        (Nat.le_trans (Nat.le_of_eq (count_true_set (Bool.not_eq_true _ ▸ h))) (Nat.le_succ _)))
      (fun acc _ hrec => match acc with
        | Except.error _ => True.intro
        | Except.ok _ => Except.allP_mp dfsFrom_count (fun _ h2 => Nat.le_trans h2 hrec)
      )
    ))


theorem dfsFrom_err_correct {a: Nat} {r: NatCDFA a} {p: Fin r.n} {l: List (Fin a)}
  {visited: Vector Bool r.n} (h: p = r.advance l.reverse):
    {fuel: Nat} → fuel > visited.count false → (dfsFrom r p l visited fuel).allEP (fun u => r.accepts u)
  | 0 => fun hf => False.elim (Nat.not_lt_zero _ hf)
  | fuel + 1 => fun hf =>
    iteInduction (fun _ => True.intro) (fun nv => iteInduction
      (fun h2 => have concl: r.f (r.advance l.reverse) = true := h ▸ h2; concl)
      (fun _ => (Fin.foldlM_induction
        (fun (w: Except _ _) _ => w.allEP (fun u => r.accepts u) ∧ w.allP (fun acc => fuel > acc.count false))
        (Except.pure_def ▸ ⟨True.intro,
          Nat.lt_of_add_lt_add_right ((count_true_set (Bool.not_eq_true _ ▸ nv)) ▸ hf)⟩)
        (fun acc _ hrec => match acc with
          | Except.error _ => hrec
          | Except.ok _ => ⟨
              dfsFrom_err_correct
                (h ▸ List.reverse_cons ▸ NatCDFA.advance_concat.symm)
                hrec.right,
              Except.allP_mp dfsFrom_count (fun _ le => Nat.lt_of_le_of_lt le hrec.right)
            ⟩
        )).left
      )
    )


def dfs {a: Nat} (r: NatCDFA a): Option (List (Fin a)) :=
  match dfsFrom r r.i [] (Vector.replicate r.n false) (r.n + 1) with
  | Except.error l => some l
  | Except.ok _ => none


theorem dfs_some_correct {a: Nat} {r: NatCDFA a}: (dfs r).all r.accepts :=
  have concl: (dfsFrom r r.i [] (Vector.replicate r.n false) (r.n + 1)).allEP (fun u => r.accepts u) :=
    dfsFrom_err_correct (rfl: r.i = r.advance [].reverse) (Nat.lt_succ_of_le (Vector.count_le_size))
  match eq: dfsFrom r r.i [] (Vector.replicate r.n false) (r.n + 1) with
  | Except.ok _ => dfs.eq_def r ▸ eq ▸ rfl
  | Except.error _ => dfs.eq_def r ▸ eq ▸ concl


theorem dfs_none_correct {a: Nat} {r: NatCDFA a} (h: dfs r = none):
    ∀ l: List (Fin a), r.accepts l = false :=
  match eq: dfsFrom r r.i [] (Vector.replicate r.n false) (r.n + 1) with
    | Except.ok table =>
      have h: okInvariant r [] table := eq.subst (dfsFrom_ok_correct [] (fun _ _ v =>
          False.elim (Bool.false_ne_true (Vector.get_replicate.symm.trans v))))
      have hs: table.get r.i = true := eq.subst dfsFrom_step
      let rec propagate (u: List (Fin a)): table.get (r.advance u) = true :=
        match List.eq_nil_or_concat u with
        | .inl eq2 => eq2 ▸ hs
        | .inr ⟨s, b, eq2⟩ =>
          eq2 ▸ List.concat_eq_append ▸ NatCDFA.advance_concat ▸
            (h (r.advance s) List.not_mem_nil (propagate s)).right b
        termination_by u.length
      fun l => Bool.not_eq_true _ ▸ (h (r.advance l) List.not_mem_nil (propagate l)).left
    | Except.error _ => nomatch (eq ▸ dfs.eq_def r ▸ h)


public section
namespace NatCDFA

inductive SearchResult {a: Nat} (r: NatCDFA a) where
  | word: (l: List (Fin a)) → r.accepts l = true → SearchResult r
  | empty: (∀ l: List (Fin a), r.accepts l = false) → SearchResult r


def search {a: Nat} (r: NatCDFA a): SearchResult r :=
  match eq: dfs r with
  | some w => SearchResult.word w (
      have concl: Option.all r.accepts (some w) := eq ▸ dfs_some_correct
      concl
    )
  | none => SearchResult.empty (dfs_none_correct eq)

end NatCDFA
end
