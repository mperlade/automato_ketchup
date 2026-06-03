/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

@[expose]
public section

structure NatNFA (a: Nat) where
  n: Nat
  δ: Fin n → Fin a → (Array (Fin n))
  i: Fin n → Bool
  f: Fin n → Bool

namespace NatNFA

def path {a: Nat} (r: NatNFA a) (p q: Fin r.n):
    (l: List (Fin a)) → Prop
  | [] => p = q
  | b::t => ∃ u: Fin r.n, u ∈ r.δ p b ∧ r.path u q t


theorem join_paths {a: Nat} {r: NatNFA a} {i j k: Fin r.n} {u v: List (Fin a)}:
    r.path i j u → r.path j k v → r.path i k (u ++ v) :=
  match u with
  | [] => fun eq h => eq ▸ h
  | _::_ => fun ⟨u, h1, h2⟩ h => ⟨u, h1, join_paths h2 h⟩


def successfulPath {a: Nat} (r: NatNFA a) (p q: Fin r.n) (l: List (Fin a)): Prop :=
  r.path p q l ∧ r.i p ∧ r.f q


def accepts {a: Nat} (r: NatNFA a) (l: List (Fin a)): Prop :=
  ∃ p q: Fin r.n, r.successfulPath p q l

end NatNFA
end
