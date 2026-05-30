/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.CDFA

def constructProduct {a: Nat} (r s: CDFA a) (p: Bool → Bool → Bool): CDFA a := {
  σ := r.σ × s.σ
  finite := inferInstance
  δ := fun (i, j) b => (r.δ i b, s.δ j b)
  i := (r.i, s.i)
  f := fun (i, j) => p (r.f i) (s.f j)
}


theorem product_advanceFrom {a: Nat} {r s: CDFA a} {p: Bool → Bool → Bool}
  {i: r.σ} {j: s.σ}:
    {l: List (Fin a)} → (constructProduct r s p).advanceFrom (i, j) l =
      (r.advanceFrom i l, s.advanceFrom j l)
  | [] => rfl
  | _::t => product_advanceFrom (l := t)


theorem product_accepts {a: Nat} {r s: CDFA a} {p: Bool → Bool → Bool} {l: List (Fin a)}:
    (constructProduct r s p).accepts l = p (r.accepts l) (s.accepts l) :=
  congrArg (constructProduct r s p).f product_advanceFrom


public section
namespace CDFA

structure ProductResult {a: Nat} (r s: CDFA a) (p: Bool → Bool → Bool) where
  product: CDFA a
  correct: ∀ l: List (Fin a), product.accepts l = p (r.accepts l) (s.accepts l)


def product {a: Nat} (r s: CDFA a) (p: Bool → Bool → Bool): ProductResult r s p := {
  product := constructProduct r s p
  correct := fun _ => product_accepts
}

end CDFA
end
