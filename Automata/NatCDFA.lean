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


theorem NatCDFA.advanceFrom_concat {a: Nat} {r: NatCDFA a} {q: Fin r.n} {f: List (Fin a)} {b: Fin a}:
    r.advanceFrom q (f ++ [b]) = r.δ (r.advanceFrom q f) b :=
  match f with
  | [] => rfl
  | _::_ => List.cons_append ▸ NatCDFA.advanceFrom_concat


def NatCDFA.morphism {a: Nat} (r s: NatCDFA a) (f: Fin r.n → Fin s.n): Prop :=
  ∀ l: List (Fin a), f (r.advance l) = s.advance l ∧ r.accepts l = s.accepts l
