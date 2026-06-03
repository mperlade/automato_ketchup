/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.NatNFA
public import AutoKchp.NatEpsNFA
import AutoKchp.Internal.Util
import AutoKchp.Internal.Warshall
import AutoKchp.Internal.HeapSort


def collectEpsilon {a: Nat} (r: NatEpsNFA a): Vector (Vector Bool r.n) r.n :=
  Vector.ofFn (fun i =>
    (r.δ i none).foldl (fun acc (j: Fin r.n) => acc.set j true) ((Vector.replicate r.n false).set i true)
  )


theorem collectEpsilon_correct {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}:
    ((collectEpsilon r).get i).get j ↔ j = i ∨ j ∈ r.δ i none :=
  Vector.get_ofFn ▸ (
    let motive (p: Nat) (acc: Vector Bool r.n): Prop :=
      acc.get j ↔ j = i ∨ (∃ q: Nat, q < p ∧ some j = (r.δ i none)[q]?)
    have ind: motive (r.δ i none).size ((r.δ i none).foldl (fun acc (j: Fin r.n) => acc.set j true)
        ((Vector.replicate r.n false).set i true)) := Array.foldl_induction motive
      ⟨
        fun h => if eq: j = i then Or.inl eq else
          False.elim (Bool.false_ne_true (Vector.get_replicate.symm.trans
            ((Vector.get_set_of_ne (Ne.symm eq)).symm.trans h))),
        fun h => have eq: j = i := h.resolve_right (fun ⟨q, hq, _⟩ => Nat.not_lt_zero q hq)
          eq ▸ Vector.get_set_self,
      ⟩
      (fun p acc hrec => if eq: (r.δ i none)[p] = j then
        ⟨
          fun _ => have eq2 := Array.getElem?_eq_some_iff.mpr ⟨_, eq⟩
            Or.inr ⟨p, Nat.lt_succ_self p, eq2.symm⟩,
          fun _ => eq ▸ Vector.get_set_self
        ⟩
      else
        have concl: (acc.set (r.δ i none)[p] true).get j ↔ j = i ∨ ∃ q, q < p.val + 1 ∧ some j = (r.δ i none)[q]? :=
          (Vector.get_set_of_ne eq).symm ▸ hrec.trans (or_congr_right ⟨
            fun ⟨q, hq, eq2⟩ => ⟨q, Nat.lt_succ_of_lt hq, eq2⟩,
            fun ⟨q, hq, eq2⟩ => ⟨q, (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq)).resolve_right
              (mt (fun eq3 => have ⟨_, c⟩ := Array.getElem?_eq_some_iff.mp (eq3 ▸ eq2).symm; c) eq), eq2⟩,
          ⟩)
        concl
      )
    ind.trans (or_congr_right ⟨
      fun ⟨_, _, eq⟩ => Array.mem_of_getElem? eq.symm,
      fun mem => have ⟨q, eq⟩ := Array.getElem?_of_mem mem
        have ⟨hq, _⟩ := Array.getElem?_eq_some_iff.mp eq
        ⟨q, hq, eq.symm⟩
    ⟩)
  )


--Reflexive and transitive closure of epsilon transition graph
def epsilonClosureTable {a: Nat} (r: NatEpsNFA a): Vector (Vector Bool r.n) r.n :=
  warshall (collectEpsilon r)


inductive epsilonPath {a: Nat} (r: NatEpsNFA a): Fin r.n → Fin r.n → Prop where
  | refl (i: Fin r.n): epsilonPath r i i
  | eps {i j k: Fin r.n}: j ∈ r.δ i none → epsilonPath r j k → epsilonPath r i k


theorem epsilonPath_trans {a: Nat} {r: NatEpsNFA a} {i j k: Fin r.n} (h: epsilonPath r j k):
    epsilonPath r i j → epsilonPath r i k
  | epsilonPath.refl _ => h
  | epsilonPath.eps h1 h2 => epsilonPath.eps h1 (epsilonPath_trans h h2)


theorem epsilonPath_of_transitivePath {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}:
    transitivePath (collectEpsilon r) i j → epsilonPath r i j
  | transitivePath.base h => match collectEpsilon_correct.mp h with
    | .inl eq => eq ▸ epsilonPath.refl i
    | .inr mem => epsilonPath.eps mem (epsilonPath.refl j)
  | transitivePath.trans h1 h2 => epsilonPath_trans
    (epsilonPath_of_transitivePath h2) (epsilonPath_of_transitivePath h1)


theorem transitivePath_of_epsilonPath {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}:
    epsilonPath r i j → transitivePath (collectEpsilon r) i j
  | epsilonPath.refl i => transitivePath.base (collectEpsilon_correct.mpr (Or.inl rfl))
  | epsilonPath.eps h1 h2 => transitivePath.trans
    (transitivePath.base (collectEpsilon_correct.mpr (Or.inr h1)))
    (transitivePath_of_epsilonPath h2)


theorem epsilonClosureTable_correct {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}:
    ((epsilonClosureTable r).get i).get j ↔ epsilonPath r i j :=
  (warshall_correct i j).trans ⟨epsilonPath_of_transitivePath, transitivePath_of_epsilonPath⟩


def epsilonClosure {a: Nat} (r: NatEpsNFA a): Vector (Array (Fin r.n)) r.n :=
  (epsilonClosureTable r).map (fun v2 =>
    Fin.foldl r.n (fun acc i => if v2.get i then acc.push i else acc) #[])


theorem epsilonClosure_correct {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}:
    j ∈ (epsilonClosure r).get i ↔ epsilonPath r i j :=
  Iff.trans (
    let motive (acc: Array (Fin r.n)) (k: Nat) := j ∈ acc ↔ j < k ∧ ((epsilonClosureTable r).get i).get j
    have ind: motive (Fin.foldl r.n (fun acc k =>
        if ((epsilonClosureTable r).get i).get k then acc.push k else acc) #[]) r.n :=
      Fin.foldl_induction motive
        ⟨fun mem => False.elim (Array.not_mem_empty _ mem), fun ⟨lt, _⟩ => False.elim (Nat.not_lt_zero j lt)⟩
        (fun _ k hrec =>
          iteInduction (motive := fun acc => motive acc k.succ)
            (fun pos => Array.mem_push.trans ⟨
              fun
                | .inl mem => have ⟨h1, h2⟩ := hrec.mp mem
                  ⟨Nat.lt_succ_of_lt h1, h2⟩
                | .inr eq => ⟨eq ▸ Nat.lt_succ_self _, eq ▸ pos⟩,
              fun ⟨h1, h2⟩ => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h1) with
                | .inl lt => Or.inl (hrec.mpr ⟨lt, h2⟩)
                | .inr eq => Or.inr (Fin.eq_of_val_eq eq)
            ⟩)
            (fun neg => hrec.trans (and_congr_left (fun pos => ⟨Nat.lt_succ_of_lt,
              fun h => (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h)).resolve_right
                (fun eq2 => neg ((Fin.eq_of_val_eq eq2) ▸ pos))⟩)))
        )
    Vector.get_map ▸ ind.trans ⟨And.right, fun h => ⟨j.isLt, h⟩⟩
  ) epsilonClosureTable_correct


def newTransitions {a: Nat} (r: NatEpsNFA a) (ec: Vector (Array (Fin r.n)) r.n):
    Vector (Vector (Array (Fin r.n)) a) r.n :=
  ec.map (fun cl => Vector.ofFn (fun b => canonicalize (
    cl.foldl (fun acc i => acc.append (r.δ i (some b))) #[]
  )))


theorem newTransitions_correct {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n} {b: Fin a}
  {ec: Vector (Array (Fin r.n)) r.n} (h: ∀ u v: Fin r.n, v ∈ ec.get u ↔ epsilonPath r u v):
    j ∈ ((newTransitions r ec).get i).get b ↔ ∃ u: Fin r.n, epsilonPath r i u ∧ j ∈ r.δ u (some b) :=
  let motive (k: Nat) (acc: Array (Fin r.n)): Prop :=
      j ∈ acc ↔ ∃ u: Fin r.n, (∃ z: Nat, z < k ∧ (ec.get i)[z]? = some u) ∧ j ∈ r.δ u (some b)
  have ind: motive (ec.get i).size
      ((ec.get i).foldl (fun acc k => acc.append (r.δ k (some b))) #[]) :=
    Array.foldl_induction motive
      ⟨
        fun mem => False.elim (Array.not_mem_empty _ mem),
        fun ⟨_, ⟨_, hz, _⟩, _⟩ => False.elim (Nat.not_lt_zero _ hz)
      ⟩
      (fun k acc hrec =>
        Array.mem_append.trans ⟨
          fun
          | .inl h => have ⟨u, ⟨z, lt, hz⟩, hu⟩ := hrec.mp h;
            ⟨u, ⟨z, Nat.lt_succ_of_lt lt, hz⟩, hu⟩
          | .inr h => ⟨(ec.get i)[k], ⟨k, Nat.lt_succ_self _,
            Array.getElem?_eq_getElem _⟩, h⟩,
          fun ⟨u, ⟨z, lt, hz⟩, hu⟩ => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt) with
          | .inl lt => Or.inl (hrec.mpr ⟨u, ⟨z, lt, hz⟩, hu⟩)
          | .inr eq => have ⟨_, eq2⟩ := eq ▸ Array.getElem?_eq_some_iff.mp hz
            Or.inr (eq2 ▸ hu)
        ⟩
      )
  Vector.get_map ▸ Vector.get_ofFn ▸ mem_canonicalize.trans (ind.trans ⟨
    fun ⟨u, ⟨_, _, hz⟩, hu2⟩ => ⟨u, (h i u).mp (Array.mem_of_getElem? hz), hu2⟩,
    fun ⟨u, hu1, hu2⟩ =>
      have ⟨z, hz⟩ := Array.getElem?_of_mem ((h i u).mpr hu1)
      have ⟨lt, _⟩ := Array.getElem?_eq_some_iff.mp hz
      ⟨u, ⟨z, lt, hz⟩, hu2⟩
  ⟩)


def newFinal {a: Nat} (r: NatEpsNFA a) (ec: Vector (Array (Fin r.n)) r.n):
    Vector Bool r.n :=
  Vector.ofFn (fun i => (ec.get i).any r.f)


theorem newFinal_correct {a: Nat} {r: NatEpsNFA a} {i: Fin r.n}
  {ec: Vector (Array (Fin r.n)) r.n} (h: ∀ u v: Fin r.n, v ∈ ec.get u ↔ epsilonPath r u v):
    (newFinal r ec).get i ↔ ∃ u: Fin r.n, epsilonPath r i u ∧ r.f u :=
  Vector.get_ofFn ▸ Array.any_iff_exists.trans ⟨
    fun ⟨p, _, _, _, hp⟩ => ⟨(ec.get i)[p], (h i _).mp (Array.getElem_mem _), hp⟩,
    fun ⟨u, hu1, hu2⟩ =>
      have ⟨p, hp1, hp2⟩ := Array.getElem_of_mem ((h i u).mpr hu1)
      ⟨p, hp1, Nat.zero_le _, hp1, hp2 ▸ hu2⟩
  ⟩


theorem path_of_epsilonPath {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}:
    epsilonPath r i j → r.path i j []
  | epsilonPath.refl i => NatEpsNFA.path.refl i
  | epsilonPath.eps h1 h2 => NatEpsNFA.path.eps h1 (path_of_epsilonPath h2)


theorem path_nil {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n} {l: List (Fin a)} (h: l = []):
    r.path i j l → epsilonPath r i j
  | NatEpsNFA.path.refl i => epsilonPath.refl i
  | NatEpsNFA.path.eps h1 h2 => epsilonPath.eps h1 (path_nil h h2)


theorem path_nil' {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}:
    r.path i j [] ↔ epsilonPath r i j :=
  ⟨
    path_nil rfl,
    path_of_epsilonPath,
  ⟩


theorem path_cons {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n} {l: List (Fin a)}
  {b: Fin a} {t: List (Fin a)} (h: l = b::t):
    r.path i j l → ∃ u v: Fin r.n, epsilonPath r i u ∧ v ∈ r.δ u (some b) ∧ r.path v j t
  | NatEpsNFA.path.trans (u := k) h1 h2 =>
    ⟨i, k, epsilonPath.refl i, List.head_eq_of_cons_eq h ▸ h1, List.tail_eq_of_cons_eq h ▸ h2⟩
  | NatEpsNFA.path.eps h1 h2 => have ⟨u, v, h3, h4, h5⟩ := path_cons h h2
    ⟨u, v, epsilonPath.eps h1 h3, h4, h5⟩


theorem path_cons' {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n} {b: Fin a} {t: List (Fin a)}:
    r.path i j (b::t) ↔ ∃ u v: Fin r.n, epsilonPath r i u ∧ v ∈ r.δ u (some b) ∧ r.path v j t :=
  ⟨
    path_cons rfl,
    fun ⟨_, _, h1, h2, h3⟩ => NatEpsNFA.join_paths (path_of_epsilonPath h1)
      (NatEpsNFA.path.trans h2 h3)
  ⟩


theorem newTransitions_correct2 {a: Nat} {r: NatEpsNFA a} {i j: Fin r.n}
  {ec: Vector (Array (Fin r.n)) r.n} {b: Fin a} {t: List (Fin a)}
  (h: ∀ u v: Fin r.n, v ∈ ec.get u ↔ epsilonPath r u v):
    r.path i j (b::t) ↔  ∃ u: Fin r.n, u ∈ ((newTransitions r ec).get i).get b ∧ r.path u j t :=
  path_cons'.trans ⟨
    fun ⟨u, v, h1, h2, h3⟩ => ⟨v, (newTransitions_correct h).mpr ⟨u, h1, h2⟩, h3⟩,
    fun ⟨u, h1, h2⟩ => have ⟨v, h3, h4⟩ := (newTransitions_correct h).mp h1
      ⟨v, u, h3, h4, h2⟩,
  ⟩


theorem newFinal_correct2 {a: Nat} {r: NatEpsNFA a} {i: Fin r.n}
  {ec: Vector (Array (Fin r.n)) r.n} (h: ∀ u v: Fin r.n, v ∈ ec.get u ↔ epsilonPath r u v):
    (∃ j: Fin r.n, r.path i j [] ∧ r.f j) ↔ (newFinal r ec).get i :=
  Iff.trans (exists_congr (fun _ => and_congr_left' path_nil')) (newFinal_correct h).symm


def constructNFA {a: Nat} (r: NatEpsNFA a): NatNFA a :=
  let ec := epsilonClosure r
  let delta := newTransitions r ec
  let final := newFinal r ec
  {
    n := r.n
    δ := fun i b => (delta.get i).get b
    i := r.i
    f := fun i => final.get i
  }


theorem constructNFA_acceptsFrom {a: Nat} {r: NatEpsNFA a} {i: Fin r.n} {l: List (Fin a)}:
    (∃ j: Fin r.n, (constructNFA r).path i j l ∧ (constructNFA r).f j) ↔
    (∃ j: Fin r.n, r.path i j l ∧ r.f j) :=
  match l with
  | [] => Iff.trans ⟨
      fun ⟨_, eq, hi⟩ => eq ▸ hi,
      fun hi => ⟨i, rfl, hi⟩
    ⟩ (newFinal_correct2 (fun _ _ => epsilonClosure_correct)).symm
  | _::_ => Iff.trans ⟨
      fun ⟨j, ⟨u, h1, h2⟩, h3⟩ => have ⟨j2, h4, h5⟩ := constructNFA_acceptsFrom.mp ⟨j, h2, h3⟩
        ⟨j2, ⟨u, h1, h4⟩, h5⟩,
      fun ⟨j, ⟨u, h1, h2⟩, h3⟩ => have ⟨j2, h4, h5⟩ := constructNFA_acceptsFrom.mpr ⟨j, h2, h3⟩
        ⟨j2, ⟨u, h1, h4⟩, h5⟩
    ⟩ (exists_congr (fun _ => and_congr_left'
      (newTransitions_correct2 (fun _ _ => epsilonClosure_correct)).symm))


theorem constructNFA_accepts {a: Nat} {r: NatEpsNFA a}:
    (constructNFA r).accepts = r.accepts :=
  funext (fun _ => propext ⟨
    fun ⟨i, j, hp, hi, hj⟩ => have ⟨j2, hp2, hj2⟩ := constructNFA_acceptsFrom.mp ⟨j, hp, hj⟩; ⟨i, j2, hp2, hi, hj2⟩,
    fun ⟨i, j, hp, hi, hj⟩ => have ⟨j2, hp2, hj2⟩ := constructNFA_acceptsFrom.mpr ⟨j, hp, hj⟩; ⟨i, j2, hp2, hi, hj2⟩,
  ⟩)


public section
namespace NatEpsNFA

structure ToNFAResult {a: Nat} (r: NatEpsNFA a) where
  nfa: NatNFA a
  correct: nfa.accepts = r.accepts


def toNFA {a: Nat} (r: NatEpsNFA a): ToNFAResult r := {
  nfa := constructNFA r
  correct := constructNFA_accepts
}

end NatEpsNFA
end
