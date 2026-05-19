/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

import AutoKchp.Internal.Counting

theorem fin_finite {n: Nat}: ∀ l: List (Fin n), l.Nodup → l.length ≤ n := fun _ hl =>
    List.card_eq_length_of_nodup hl ▸
  List.card_map_inj Fin.val (fun _ _ => Fin.val_inj.mp) ▸
  List.card_at_most (fun _ hi => have ⟨j, _, eq⟩ := List.mem_map.mp hi; eq ▸ j.isLt)


public section

class FiniteHashable (α: Type) extends Hashable α where
  cardinal: Nat
  finite: ∀ l: List α, l.Nodup → l.length ≤ cardinal


@[no_expose]
instance {n: Nat}: FiniteHashable (Fin n) := {
  cardinal := n
  finite := fin_finite
}


end
