/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

@[expose]
public section

structure NatNFT (a: Nat) where
  n: Nat
  δ: Fin n → Option (Fin a) → Option (Fin a) → (Array (Fin n))
  i: Fin n → Bool
  f: Fin n → Bool

namespace NatNFT

def extendsPath {a: Nat} (b: Option (Fin a)) (t: List (Fin a)) (l: List (Fin a)): Prop :=
  match b with
  | some b => match l with
    | b2::t2 => b = b2 ∧ t = t2
    | [] => False
  | none => t = l


inductive path {a: Nat} (r: NatNFT a): Fin r.n → Fin r.n → List (Fin a) → List (Fin a) → Prop where
  | refl (p: Fin r.n): r.path p p [] []
  | trans {srcb dstb: Option (Fin a)} {srct dstt: List (Fin a)}
    {src2 dst2: List (Fin a)} {p q u: Fin r.n}:
      extendsPath srcb srct src2 → extendsPath dstb dstt dst2 → u ∈ r.δ p srcb dstb →
      r.path u q srct dstt → r.path p q src2 dst2


def successfulPath {a: Nat} (r: NatNFT a) (p q: Fin r.n) (src dst: List (Fin a)): Prop :=
  r.path p q src dst ∧ r.i p ∧ r.f q


def accepts {a: Nat} (r: NatNFT a) (src dst: List (Fin a)): Prop :=
  ∃ p q: Fin r.n, r.successfulPath p q src dst

end NatNFT
end
