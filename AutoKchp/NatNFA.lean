/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

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


def successfulPath {a: Nat} (r: NatNFA a) (p q: Fin r.n) (l: List (Fin a)): Prop :=
  r.path p q l ∧ r.i p ∧ r.f q


def accepts {a: Nat} (r: NatNFA a) (l: List (Fin a)): Prop :=
  ∃ p q: Fin r.n, r.successfulPath p q l

end NatNFA
end
