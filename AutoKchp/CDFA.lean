/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

import AutoKchp.Internal.Util
public import AutoKchp.FiniteHashable

@[expose]
public section

structure CDFA (a: Nat) where
  σ: Type
  finite: FiniteHashable σ
  δ: σ → Fin a → σ
  i: σ
  f: σ → Bool


instance {a: Nat} {r: CDFA a}: FiniteHashable r.σ := r.finite


namespace CDFA

def advanceFrom {a: Nat} (r: CDFA a) (q: r.σ): List (Fin a) → r.σ
  | a::t => r.advanceFrom (r.δ q a) t
  | [] => q


def acceptsFrom {a: Nat} (r: CDFA a) (q: r.σ) (w: List (Fin a)): Bool :=
  r.f (r.advanceFrom q w)


def advance {a: Nat} (r: CDFA a): List (Fin a) → r.σ := r.advanceFrom r.i


def accepts {a: Nat} (r: CDFA a): List (Fin a) → Bool := r.acceptsFrom r.i


theorem advanceFrom_append {a: Nat} {r: CDFA a} {q: r.σ} {f₁ f₂: List (Fin a)}:
    r.advanceFrom q (f₁ ++ f₂) = r.advanceFrom (r.advanceFrom q f₁) f₂ :=
  match f₁ with
  | [] => rfl
  | _::_ => List.cons_append ▸ advanceFrom_append


theorem advanceFrom_concat {a: Nat} {r: CDFA a} {q: r.σ} {f: List (Fin a)} {b: Fin a}:
    r.advanceFrom q (f ++ [b]) = r.δ (r.advanceFrom q f) b :=
  advanceFrom_append


theorem advance_concat {a: Nat} {r: CDFA a} {f: List (Fin a)} {b: Fin a}:
    r.advance (f ++ [b]) = r.δ (r.advance f) b :=
  advanceFrom_concat


def morphism {a: Nat} (r s: CDFA a) (f: r.σ → s.σ): Prop :=
  ∀ l: List (Fin a), f (r.advance l) = s.advance l ∧ r.accepts l = s.accepts l


def existsMorphism {a: Nat} (r s: CDFA a): Prop :=
  ∃ f: r.σ → s.σ, CDFA.morphism r s f


end CDFA

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
  | _::_ => List.cons_append ▸ advanceFrom_append


theorem advanceFrom_concat {a: Nat} {r: NatCDFA a} {q: Fin r.n} {f: List (Fin a)} {b: Fin a}:
    r.advanceFrom q (f ++ [b]) = r.δ (r.advanceFrom q f) b :=
  advanceFrom_append


theorem advance_concat {a: Nat} {r: NatCDFA a} {f: List (Fin a)} {b: Fin a}:
    r.advance (f ++ [b]) = r.δ (r.advance f) b :=
  advanceFrom_concat


def morphism {a: Nat} (r s: NatCDFA a) (f: Fin r.n → Fin s.n): Prop :=
  ∀ l: List (Fin a), f (r.advance l) = s.advance l ∧ r.accepts l = s.accepts l


def existsMorphism {a: Nat} (r s: NatCDFA a): Prop :=
  ∃ f: Fin r.n → Fin s.n, NatCDFA.morphism r s f


def minimal {a: Nat} (r: NatCDFA a): Prop :=
  ∀ s: NatCDFA a, s.accepts = r.accepts → NatCDFA.existsMorphism s r


def toCDFA {a: Nat} (r: NatCDFA a): CDFA a := {
  σ := Fin r.n
  finite := inferInstance
  δ := r.δ
  i := r.i
  f := r.f
}


theorem advanceFrom_toCDFA {a: Nat} {r: NatCDFA a} {q: Fin r.n}:
    {l: List (Fin a)} → r.toCDFA.advanceFrom q l = r.advanceFrom q l
  | [] => rfl
  | _::t => advanceFrom_toCDFA (l := t)


theorem acceptsFrom_toCDFA {a: Nat} {r: NatCDFA a} {q: Fin r.n} {l: List (Fin a)}:
    r.toCDFA.acceptsFrom q l = r.acceptsFrom q l :=
  congrArg r.f advanceFrom_toCDFA


theorem advance_toCDFA {a: Nat} {r: NatCDFA a} {l: List (Fin a)}:
    r.toCDFA.advance l = r.advance l :=
  advanceFrom_toCDFA


theorem accepts_toCDFA {a: Nat} {r: NatCDFA a} {l: List (Fin a)}:
    r.toCDFA.accepts l = r.accepts l :=
  acceptsFrom_toCDFA


theorem morphism_toCDFA {a: Nat} {r s: NatCDFA a} {f: Fin r.n → Fin s.n}:
    morphism r s f ↔ CDFA.morphism r.toCDFA s.toCDFA f :=
  forall_congr' (fun _ => and_congr
    (advance_toCDFA ▸ advance_toCDFA ▸ Iff.rfl)
    (accepts_toCDFA ▸ accepts_toCDFA ▸ Iff.rfl)
  )


theorem existsMorphism_toCDFA {a: Nat} {r s: NatCDFA a}:
    existsMorphism r s ↔ CDFA.existsMorphism r.toCDFA s.toCDFA :=
  exists_congr (fun _ => morphism_toCDFA)

end NatCDFA
end
