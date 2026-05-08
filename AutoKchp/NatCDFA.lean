/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

import AutoKchp.Util

@[expose]
public section

structure NatCDFA (a: Nat) where
  n: Nat
  δ: Fin n → Fin a → Fin n
  i: Fin n
  f: Fin n → Bool

namespace NatCDFA

def advanceFrom {a: Nat} (r: NatCDFA a) (q: Fin r.n): List (Fin a) → Fin r.n
  | a::t => r.advanceFrom (r.δ q a) t
  | [] => q


def acceptsFrom {a: Nat} (r: NatCDFA a) (q: Fin r.n) (w: List (Fin a)): Bool :=
  r.f (r.advanceFrom q w)


def advance {a: Nat} (r: NatCDFA a): List (Fin a) → Fin r.n := r.advanceFrom r.i


def accepts {a: Nat} (r: NatCDFA a): List (Fin a) → Bool := r.acceptsFrom r.i


def concretize {a: Nat} (r: NatCDFA a): NatCDFA a :=
  let transitions := Vector.ofFn (fun i => Vector.ofFn (fun b => r.δ i b))
  let final := Vector.ofFn r.f
  {
    n := r.n
    δ := fun i b => (transitions.get i).get b
    i := r.i
    f := fun i => final.get i
  }


theorem concretize_id {a: Nat} {r: NatCDFA a}: r.concretize = r :=
  r.casesOn (fun n δ i t => mk.injEq _ _ _ _ n δ i t ▸ ⟨
      rfl,
      heq_of_eq (funext fun _ => (funext fun _ => Vector.get_ofFn ▸ Vector.get_ofFn)),
      heq_of_eq rfl,
      heq_of_eq (funext fun _ => Vector.get_ofFn)
    ⟩
  )


theorem advanceFrom_append {a: Nat} {r: NatCDFA a} {q: Fin r.n} {f₁ f₂: List (Fin a)}:
    r.advanceFrom q (f₁ ++ f₂) = r.advanceFrom (r.advanceFrom q f₁) f₂ :=
  match f₁ with
  | [] => rfl
  | _::_ => List.cons_append ▸ NatCDFA.advanceFrom_append


theorem advanceFrom_concat {a: Nat} {r: NatCDFA a} {q: Fin r.n} {f: List (Fin a)} {b: Fin a}:
    r.advanceFrom q (f ++ [b]) = r.δ (r.advanceFrom q f) b :=
  NatCDFA.advanceFrom_append


theorem advance_concat {a: Nat} {r: NatCDFA a} {f: List (Fin a)} {b: Fin a}:
    r.advance (f ++ [b]) = r.δ (r.advance f) b :=
  NatCDFA.advanceFrom_concat


def morphism {a: Nat} (r s: NatCDFA a) (f: Fin r.n → Fin s.n): Prop :=
  ∀ l: List (Fin a), f (r.advance l) = s.advance l ∧ r.accepts l = s.accepts l


def existsMorphism {a: Nat} (r s: NatCDFA a): Prop :=
  ∃ f: Fin r.n → Fin s.n, NatCDFA.morphism r s f


def minimal {a: Nat} (r: NatCDFA a): Prop :=
  ∀ s: NatCDFA a, s.accepts = r.accepts → NatCDFA.existsMorphism s r


end NatCDFA
end
