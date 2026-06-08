/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.FiniteHashable

@[expose]
public section

structure NFA (a: Nat) where
  σ: Type
  finite: FiniteHashable σ
  δ: σ → Fin a → Array σ
  i: Array σ
  f: σ → Bool


namespace NFA

instance {a: Nat} {r: NFA a}: FiniteHashable r.σ := r.finite


def path {a: Nat} (r: NFA a) (p q: r.σ): List (Fin a) → Prop
  | [] => p = q
  | b::t => ∃ u: r.σ, u ∈ r.δ p b ∧ r.path u q t


def successfulPath {a: Nat} (r: NFA a) (p q: r.σ) (l: List (Fin a)): Prop :=
  r.path p q l ∧ p ∈ r.i ∧ r.f q


def accepts {a: Nat} (r: NFA a) (l: List (Fin a)): Prop :=
  ∃ p q: r.σ, r.successfulPath p q l


theorem path_concat {a: Nat} {r: NFA a} {p q: r.σ} {b: Fin a}:
    {s: List (Fin a)} → r.path p q (s ++ [b]) ↔ ∃ u: r.σ, r.path p u s ∧ q ∈ r.δ u b
  | [] => ⟨fun ⟨_, h, eq⟩ => ⟨p, rfl, eq ▸ h⟩, fun ⟨_, eq, h⟩ => ⟨q, eq ▸ h, rfl⟩⟩
  | _::_ => ⟨
    fun ⟨v, hv1, hv2⟩ =>
      have ⟨u, hu1, hu2⟩ := path_concat.mp hv2; ⟨u, ⟨v, hv1, hu1⟩, hu2⟩,
    fun ⟨u, ⟨v, hv1, hv2⟩, hu2⟩ => ⟨v, hv1, path_concat.mpr ⟨u, hv2, hu2⟩⟩,
  ⟩

end NFA

structure NatNFA (a: Nat) where
  n: Nat
  δ: Fin n → Fin a → (Array (Fin n))
  i: Array (Fin n)
  f: Fin n → Bool

namespace NatNFA

def path {a: Nat} (r: NatNFA a) (p q: Fin r.n): List (Fin a) → Prop
  | [] => p = q
  | b::t => ∃ u: Fin r.n, u ∈ r.δ p b ∧ r.path u q t


theorem join_paths {a: Nat} {r: NatNFA a} {i j k: Fin r.n} {u v: List (Fin a)}:
    r.path i j u → r.path j k v → r.path i k (u ++ v) :=
  match u with
  | [] => fun eq h => eq ▸ h
  | _::_ => fun ⟨u, h1, h2⟩ h => ⟨u, h1, join_paths h2 h⟩


def successfulPath {a: Nat} (r: NatNFA a) (p q: Fin r.n) (l: List (Fin a)): Prop :=
  r.path p q l ∧ p ∈ r.i ∧ r.f q


def accepts {a: Nat} (r: NatNFA a) (l: List (Fin a)): Prop :=
  ∃ p q: Fin r.n, r.successfulPath p q l


theorem path_concat {a: Nat} {r: NatNFA a} {p q: Fin r.n} {b: Fin a}:
    {s: List (Fin a)} → r.path p q (s ++ [b]) ↔ ∃ u: Fin r.n, r.path p u s ∧ q ∈ r.δ u b
  | [] => ⟨fun ⟨_, h, eq⟩ => ⟨p, rfl, eq ▸ h⟩, fun ⟨_, eq, h⟩ => ⟨q, eq ▸ h, rfl⟩⟩
  | _::_ => ⟨
    fun ⟨v, hv1, hv2⟩ =>
      have ⟨u, hu1, hu2⟩ := path_concat.mp hv2; ⟨u, ⟨v, hv1, hu1⟩, hu2⟩,
    fun ⟨u, ⟨v, hv1, hv2⟩, hu2⟩ => ⟨v, hv1, path_concat.mpr ⟨u, hv2, hu2⟩⟩,
  ⟩


def toNFA {a: Nat} (r: NatNFA a): NFA a := {
  σ := Fin r.n
  finite := inferInstance
  δ := r.δ
  i := r.i
  f := r.f
}


theorem path_toNFA {a: Nat} {r: NatNFA a} {p q: Fin r.n} {l: List (Fin a)}:
    r.toNFA.path p q l ↔ r.path p q l :=
  match l with
  | [] => Iff.refl _
  | _::_ => exists_congr (fun _ => and_congr_right' path_toNFA)


theorem successfulPath_toNFA {a: Nat} {r: NatNFA a} {p q: Fin r.n} {l: List (Fin a)}:
    r.toNFA.successfulPath p q l ↔ r.successfulPath p q l :=
  and_congr_left' path_toNFA


theorem accepts_toNFA {a: Nat} {r: NatNFA a} {l: List (Fin a)}:
    r.toNFA.accepts l ↔ r.accepts l :=
  exists_congr (fun _ => exists_congr (fun _ => successfulPath_toNFA))

end NatNFA
end
