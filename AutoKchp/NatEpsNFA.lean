/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.NFA

@[expose]
public section

def NatEpsNFA (a: Nat) := NatNFA (a + 1)

namespace NatEpsNFA

def ε {a: Nat}: Fin (a + 1) := ⟨a, Nat.lt_succ_self a⟩


def char {a: Nat} (c: Fin a): Fin (a + 1) := ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩


def extractWord {a: Nat}: List (Fin (a + 1)) → List (Fin a)
  | [] => []
  | b::t => if eq: b = ε
    then extractWord t
    else ⟨b.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ b.isLt)
      (Fin.val_ne_of_ne eq)⟩::(extractWord t)


theorem extractWord_cons_ε {a: Nat} {l: List (Fin (a + 1))}:
    extractWord (ε::l) = extractWord l :=
  dif_pos rfl


theorem extractWord_cons_char {a: Nat} {l: List (Fin (a + 1))} {b: Fin a}:
    extractWord ((char b)::l) = b::(extractWord l) :=
  dif_neg (Fin.ne_of_val_ne (Nat.ne_of_lt b.isLt))


theorem extractWord_append {a: Nat} {f g: List (Fin (a + 1))}:
    extractWord (f ++ g) = extractWord f ++ extractWord g :=
  match f with
  | [] => rfl
  | b::t => if eq: b = ε then
      (dif_pos eq).trans ((extractWord_append (f := t) (g := g)).trans
        (congrArg (· ++ extractWord g) (dif_pos eq (t := fun _ => extractWord t)).symm))
    else
      (dif_neg eq).trans ((List.cons_eq_cons.mpr ⟨rfl, extractWord_append⟩).trans
        (congrArg (· ++ extractWord g) (dif_neg eq (e := fun _ => _::(extractWord t))).symm))


def path {a: Nat} (r: NatEpsNFA a): Fin r.n → Fin r.n → List (Fin a) → Prop :=
  fun p q l => ∃ u: List (Fin (a + 1)), l = extractWord u ∧ (NatNFA.path r p q u)


theorem join_paths {a: Nat} {r: NatEpsNFA a} {i j k: Fin r.n} {u v: List (Fin a)}:
    r.path i j u → r.path j k v → r.path i k (u ++ v) :=
  fun ⟨f, eqf, hf⟩ ⟨g, eqg, hg⟩ =>
    ⟨f ++ g, eqf ▸ eqg ▸ extractWord_append.symm, NatNFA.join_paths hf hg⟩


def successfulPath {a: Nat} (r: NatEpsNFA a) (p q: Fin r.n) (l: List (Fin a)): Prop :=
  r.path p q l ∧ p ∈ r.i ∧ r.f q


def accepts {a: Nat} (r: NatEpsNFA a) (l: List (Fin a)): Prop :=
  ∃ p q: Fin r.n, r.successfulPath p q l

end NatEpsNFA
end
