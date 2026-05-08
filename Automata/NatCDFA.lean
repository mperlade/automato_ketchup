import Automata.Util

structure NatCDFA (a: Nat) where
  n: Nat
  δ: Fin n → Fin a → Fin n
  i: Fin n
  t: Fin n → Bool


def NatCDFA.advanceFrom {a: Nat} (r: NatCDFA a) (q: Fin r.n): List (Fin a) → Fin r.n
  | a::f => r.advanceFrom (r.δ q a) f
  | [] => q


def NatCDFA.acceptsFrom {a: Nat} (r: NatCDFA a) (q: Fin r.n) (w: List (Fin a)): Bool :=
  r.t (r.advanceFrom q w)


def NatCDFA.advance {a: Nat} (r: NatCDFA a): List (Fin a) → Fin r.n := r.advanceFrom r.i


def NatCDFA.accepts {a: Nat} (r: NatCDFA a): List (Fin a) → Bool := r.acceptsFrom r.i


def NatCDFA.concretize {a: Nat} (r: NatCDFA a): NatCDFA a :=
  let transitions := Vector.ofFn (fun i => Vector.ofFn (fun b => r.δ i b))
  let final := Vector.ofFn r.t
  {
    n := r.n
    δ := fun i b => (transitions.get i).get b
    i := r.i
    t := fun i => final.get i
  }


theorem NatCDFA.concretize_id {a: Nat} {r: NatCDFA a}: r.concretize = r :=
  r.casesOn (fun n δ i t => mk.injEq _ _ _ _ n δ i t ▸ ⟨
      rfl,
      heq_of_eq (funext fun _ => (funext fun _ => Vector.get_ofFn ▸ Vector.get_ofFn)),
      heq_of_eq rfl,
      heq_of_eq (funext fun _ => Vector.get_ofFn)
    ⟩
  )


theorem NatCDFA.advanceFrom_append {a: Nat} {r: NatCDFA a} {q: Fin r.n} {f₁ f₂: List (Fin a)}:
    r.advanceFrom q (f₁ ++ f₂) = r.advanceFrom (r.advanceFrom q f₁) f₂ :=
  match f₁ with
  | [] => rfl
  | _::_ => List.cons_append ▸ NatCDFA.advanceFrom_append


theorem NatCDFA.advanceFrom_concat {a: Nat} {r: NatCDFA a} {q: Fin r.n} {f: List (Fin a)} {b: Fin a}:
    r.advanceFrom q (f ++ [b]) = r.δ (r.advanceFrom q f) b :=
  NatCDFA.advanceFrom_append


theorem NatCDFA.advance_concat {a: Nat} {r: NatCDFA a} {f: List (Fin a)} {b: Fin a}:
    r.advance (f ++ [b]) = r.δ (r.advance f) b :=
  NatCDFA.advanceFrom_concat


def NatCDFA.morphism {a: Nat} (r s: NatCDFA a) (f: Fin r.n → Fin s.n): Prop :=
  ∀ l: List (Fin a), f (r.advance l) = s.advance l ∧ r.accepts l = s.accepts l


def NatCDFA.existsMorphism {a: Nat} (r s: NatCDFA a): Prop :=
  ∃ f: Fin r.n → Fin s.n, NatCDFA.morphism r s f


def NatCDFA.minimal {a: Nat} (r: NatCDFA a): Prop :=
  ∀ s: NatCDFA a, s.accepts = r.accepts → NatCDFA.existsMorphism s r
