/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.NatCDFA
import AutoKchp.Moore
import AutoKchp.MorphismDfs
import AutoKchp.Util

def invertPartition {n: Nat} (p: Partition n): Vector (Option (Fin n)) p.k :=
  Fin.foldl n (fun acc i => acc.set (p.part.get i) i) (Vector.replicate p.k none)


theorem invertPartition_correct1 {n: Nat} {p: Partition n}:
    ∀ j, j ∈ p.part → ((invertPartition p).get j).isSome :=
  let motive (table: Vector (Option (Fin n)) p.k) (c: Nat) :=
    ∀ i: Fin n, i < c → (table.get (p.part.get i)).isSome
  have ind: motive (invertPartition p) n :=
    Fin.foldl_induction motive
      (fun i hi => False.elim (Nat.not_lt_zero i hi))
      (fun _ i hrec i2 hi2 => if eq: p.part.get i2 = p.part.get i then
          eq.symm ▸ Vector.get_set_self ▸ rfl
        else
          have hi2: i2 < i := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi2)
            (fun eq2 => eq (congrArg p.part.get (Fin.eq_of_val_eq eq2)))
          (Vector.get_set_of_ne (Ne.symm eq)).symm ▸ hrec i2 hi2
      )
  fun _ mem =>
    have ⟨i, eq⟩ := Vector.exists_get_of_mem mem
    eq ▸ ind i i.isLt


theorem invertPartition_correct2 {n: Nat} {p: Partition n}:
    ∀ j, ((invertPartition p).get j).all (fun i => p.part.get i = j) :=
  Fin.foldl_induction (fun (table: Vector (Option (Fin n)) p.k) _ =>
      ∀ j, (table.get j).all (fun i => p.part.get i = j))
    (fun _ => Vector.get_replicate ▸ rfl)
    (fun _ i hrec j => if eq: p.part.get i = j then
        eq ▸ Vector.get_set_self ▸ decide_eq_true rfl
      else
        (Vector.get_set_of_ne eq).symm ▸ hrec j
    )


theorem isSome_of_mem_invertPartition_normalized {n: Nat} {p: Partition n} (h: p.normalized) {o: Option (Fin n)}:
    o ∈ invertPartition p → o.isSome :=
  fun mem =>
    have ⟨j, eq⟩ := Vector.exists_get_of_mem mem
    eq ▸ (invertPartition_correct1 j (h j))


--Invert a surjective partition function
def invertNormalizedPartition {n: Nat} (p: Partition n) (h: p.normalized): Vector (Fin n) p.k :=
  (invertPartition p).attach.map (fun ⟨o, mem⟩ => o.get (isSome_of_mem_invertPartition_normalized h mem))


theorem Vector.get_map {α β} {n: Nat} {v: Vector α n} {f: α → β} {i: Fin n}:
    (v.map f).get i = f (v.get i) :=
  Vector.getElem_map f i.isLt


theorem Vector.val_get_attach {α} {n: Nat} {v: Vector α n} {i: Fin n}:
    (v.attach.get i).val = v.get i :=
  congrArg Subtype.val (Vector.getElem_attach i.isLt)


theorem invertNormalizedPartition_correct {n: Nat} {p: Partition n} (h: p.normalized):
    ∀ j, p.part.get ((invertNormalizedPartition p h).get j) = j :=
  fun j =>
    have concl: p.part.get ((Vector.map (fun x => x.val.get (isSome_of_mem_invertPartition_normalized h x.property))
        (invertPartition p).attach).get j) = j :=
      Vector.get_map ▸ Option.get_congr Vector.val_get_attach ▸
        of_decide_eq_true ((Option.all_eq_true_iff_get
        (fun i => p.part.get i = j) ((invertPartition p).get j)).mp
        (invertPartition_correct2 j) _)
    concl


def mooreMinimize {a: Nat} (r: NatCDFA a): Σ s: NatCDFA a, Fin r.n → Fin s.n :=
  let moore := computeMoore r
  let inverse := invertNormalizedPartition moore computeMoore_normalized
  ⟨
    {
      n := moore.k,
      δ := fun i b => moore.part.get (r.δ (inverse.get i) b)
      i := moore.part.get r.i
      f := fun i => r.f (inverse.get i)
    },
    fun i => moore.part.get i
  ⟩


theorem invertNormalizedPartition_rel {n: Nat} {p: Partition n} (h: p.normalized):
    ∀ i, p.rel ((invertNormalizedPartition p h).get (p.part.get i)) i :=
  fun i => invertNormalizedPartition_correct h (p.part.get i)


theorem NatCDFA.acceptsFrom_δ_eq_of_acceptsFrom_eq {a: Nat} {r: NatCDFA a} {i j: Fin r.n} {b: Fin a}:
    r.acceptsFrom i = r.acceptsFrom j → r.acceptsFrom (r.δ i b) = r.acceptsFrom (r.δ j b) :=
  fun h => funext (fun l => congrFun h (b::l))


theorem mooreMinimize_δ {a: Nat} {r: NatCDFA a} {i: Fin r.n} {b: Fin a}:
    (mooreMinimize r).fst.δ ((mooreMinimize r).snd i) b = (mooreMinimize r).snd (r.δ i b) :=
  computeMoore_correct.mpr (NatCDFA.acceptsFrom_δ_eq_of_acceptsFrom_eq
      (computeMoore_correct.mp (invertNormalizedPartition_rel _ i)))


theorem NatCDFA.t_eq_of_acceptsFrom_eq {a: Nat} {r: NatCDFA a} {i j: Fin r.n}:
    r.acceptsFrom i = r.acceptsFrom j → r.f i = r.f j :=
  fun h => congrFun h []


theorem mooreMinimize_t {a: Nat} {r: NatCDFA a} {i: Fin r.n}:
    (mooreMinimize r).fst.f ((mooreMinimize r).snd i) = r.f i :=
  NatCDFA.t_eq_of_acceptsFrom_eq (computeMoore_correct.mp
    (invertNormalizedPartition_rel _ i))


theorem mooreMinimize_advanceFrom {a: Nat} {r: NatCDFA a} {i: Fin r.n}:
    {l: List (Fin a)} → (mooreMinimize r).fst.advanceFrom ((mooreMinimize r).snd i) l =
      (mooreMinimize r).snd (r.advanceFrom i l)
  | [] => rfl
  | h::t =>
    have concl: (mooreMinimize r).fst.advanceFrom ((mooreMinimize r).fst.δ ((mooreMinimize r).snd i) h) t =
      (mooreMinimize r).snd (r.advanceFrom (r.δ i h) t) := mooreMinimize_δ ▸ mooreMinimize_advanceFrom
    concl


theorem mooreMinimize_advance {a: Nat} {r: NatCDFA a} {l: List (Fin a)}:
    (mooreMinimize r).fst.advance l = (mooreMinimize r).snd (r.advance l) :=
  mooreMinimize_advanceFrom


theorem mooreMinimize_morphism {a: Nat} {r: NatCDFA a}:
    NatCDFA.morphism r _ (mooreMinimize r).snd :=
  fun l => ⟨
    mooreMinimize_advance.symm,
    have concl: r.f (r.advanceFrom r.i l) =
        (mooreMinimize r).fst.f ((mooreMinimize r).fst.advanceFrom (mooreMinimize r).fst.i l) :=
      mooreMinimize_t ▸ congrArg (mooreMinimize r).fst.f mooreMinimize_advanceFrom.symm
    concl
  ⟩


theorem mooreMinimize_correct {a: Nat} {r: NatCDFA a} {i j: Fin r.n}:
    (mooreMinimize r).snd i = (mooreMinimize r).snd j ↔ r.acceptsFrom i = r.acceptsFrom j :=
  Iff.trans Iff.rfl computeMoore_correct


theorem mooreMinimize_minimal {a: Nat} {r: NatCDFA a}:
    (mooreMinimize r).fst.minimal := fun s hs =>
  match s.findMorphism (mooreMinimize r).fst with
  | NatCDFA.FindMorphismResult.morphism f hf => ⟨f, hf⟩
  | NatCDFA.FindMorphismResult.obstruction obs => match obs with
    | NatCDFA.MorphismObstruction.final l hl => False.elim (hl (congrFun hs l))
    | NatCDFA.MorphismObstruction.state l1 l2 hs2 hmr => False.elim (hmr (
      have h: r.acceptsFrom (r.advance l1) = r.acceptsFrom (r.advance l2) := funext fun l =>
        NatCDFA.acceptsFrom.eq_def _ (r.advance l1) _ ▸
        NatCDFA.acceptsFrom.eq_def _ (r.advance l2) _ ▸
          NatCDFA.advanceFrom_append (f₁ := l1) ▸
          NatCDFA.advanceFrom_append (f₁ := l2) ▸
            (((mooreMinimize_morphism (r := r)) (l1 ++ l)).right.trans
              (hs ▸ congrArg s.f (
                  NatCDFA.advanceFrom_append (f₁ := l1) ▸
                  NatCDFA.advanceFrom_append (f₁ := l2) ▸
                congrArg (fun w => s.advanceFrom w l) hs2
              ))
            ).trans ((mooreMinimize_morphism (r := r)) (l2 ++ l)).right.symm
      ((mooreMinimize_morphism l1).left.symm.trans
        (mooreMinimize_correct.mpr h)).trans (mooreMinimize_morphism l2).left
    ))

public section
namespace NatCDFA

structure MinimizationResult {a: Nat} (r: NatCDFA a) where
  minimized: NatCDFA a
  m: Fin r.n → Fin minimized.n
  morphism: NatCDFA.morphism r minimized m
  correct: minimized.minimal


def minimize {a: Nat} (r: NatCDFA a): NatCDFA.MinimizationResult r :=
  let m := mooreMinimize r
  {
    minimized := m.fst.concretize,
    m := m.snd,
    morphism :=
      have eq: m.fst.concretize = m.fst := concretize_id
      have morphism_heq: r.morphism m.fst.concretize ≍ r.morphism m.fst :=
          eq.symm ▸ HEq.refl (r.morphism m.fst)
      Eq.mpr (congrFun (eq_of_heq morphism_heq) m.snd) mooreMinimize_morphism
    correct := concretize_id ▸ mooreMinimize_minimal,
  }

end NatCDFA
end
