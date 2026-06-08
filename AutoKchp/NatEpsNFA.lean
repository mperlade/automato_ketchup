/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

@[expose]
public section

structure NatEpsNFA (a: Nat) where
  n: Nat
  δ: Fin n → Option (Fin a) → (Array (Fin n))
  i: Array (Fin n)
  f: Fin n → Bool

namespace NatEpsNFA

inductive path {a: Nat} (r: NatEpsNFA a): Fin r.n → Fin r.n → List (Fin a) → Prop where
  | refl (p: Fin r.n): r.path p p []
  | trans {b: Fin a} {t: List (Fin a)} {p q u: Fin r.n}:
    u ∈ r.δ p (some b) → r.path u q t → r.path p q (b::t)
  | eps {l: List (Fin a)} {p q u: Fin r.n}:
    u ∈ r.δ p none → r.path u q l → r.path p q l


theorem join_paths {a: Nat} {r: NatEpsNFA a} {i j k: Fin r.n} {u v: List (Fin a)}:
    r.path i j u → r.path j k v → r.path i k (u ++ v)
  | path.refl i => id
  | path.trans h1 h2 => fun h3 => path.trans h1 (join_paths h2 h3)
  | path.eps h1 h2 => fun h3 => path.eps h1 (join_paths h2 h3)


def successfulPath {a: Nat} (r: NatEpsNFA a) (p q: Fin r.n) (l: List (Fin a)): Prop :=
  r.path p q l ∧ p ∈ r.i ∧ r.f q


def accepts {a: Nat} (r: NatEpsNFA a) (l: List (Fin a)): Prop :=
  ∃ p q: Fin r.n, r.successfulPath p q l

end NatEpsNFA
end
