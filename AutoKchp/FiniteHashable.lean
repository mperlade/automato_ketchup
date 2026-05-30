/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

import AutoKchp.Internal.Counting
public import Std.Data.HashSet

theorem fin_finite {n: Nat}: ∀ l: List (Fin n), l.Nodup → l.length ≤ n := fun _ hl =>
    List.card_eq_length_of_nodup hl ▸
  List.card_map_inj Fin.val (fun _ _ => Fin.val_inj.mp) ▸
  List.card_at_most (fun _ hi => have ⟨j, _, eq⟩ := List.mem_map.mp hi; eq ▸ j.isLt)


theorem prod_finite {α β} [DecidableEq α] [DecidableEq β] {n m: Nat}
  (h1: ∀ l: List α, l.Nodup → l.length ≤ n) (h2: ∀ l: List β, l.Nodup → l.length ≤ m):
    ∀ l: List (α × β), l.Nodup → l.length ≤ n * m :=
  fun l hl =>
    let as := (l.map Prod.fst).dedup
    let bs := (l.map Prod.snd).dedup
    have has: as.length ≤ n := h1 as List.dedup_nodup
    have hbs: bs.length ≤ m := h2 bs List.dedup_nodup
    let l2 := (as.map (fun a => bs.map (fun b => (a, b)))).flatten
    have sub: l ⊆ l2 := fun (a, _) mem =>
      List.mem_flatten.mpr ⟨bs.map (fun b2 => (a, b2)),
        List.mem_map_of_mem (List.mem_dedup.mpr (List.mem_map_of_mem mem)),
        List.mem_map_of_mem (List.mem_dedup.mpr (List.mem_map_of_mem mem))
      ⟩
    have lens: (as.map (fun a => bs.map (fun b => (a, b)))).map List.length =
        List.replicate as.length bs.length :=
      List.eq_replicate_iff.mpr ⟨
        (List.length_map _).trans (List.length_map _),
        fun _ mem =>
          have ⟨_, _, eq⟩ := List.mem_map.mp (List.map_map ▸ mem)
          eq.symm.trans (List.length_map _)
      ⟩
    have hl2: l2.length = as.length * bs.length :=
      List.length_flatten.trans (lens ▸ List.sum_replicate_nat)
    List.card_eq_length_of_nodup hl ▸ Nat.le_trans (List.card_mono sub)
      (Nat.le_trans List.card_le_length (hl2 ▸ Nat.mul_le_mul has hbs))


public section

class FiniteHashable (α: Type) extends Hashable α, BEq α, LawfulBEq α where
  cardinal: Nat
  finite: ∀ l: List α, l.Nodup → l.length ≤ cardinal


instance {α} [FiniteHashable α]: DecidableEq α := instDecidableEqOfLawfulBEq


@[no_expose]
instance {n: Nat}: FiniteHashable (Fin n) := {
  cardinal := n
  finite := fin_finite
}


@[no_expose]
instance {α β} [h1: FiniteHashable α] [h2: FiniteHashable β]: FiniteHashable (α × β) := {
  cardinal := h1.cardinal * h2.cardinal
  finite := prod_finite h1.finite h2.finite
}

namespace FiniteHashable

theorem hashset_size_le {α} [FiniteHashable α] {s: Std.HashSet α}: s.size ≤ cardinal α :=
  Std.HashSet.length_toList (α := α) ▸ finite s.toList (Std.HashSet.distinct_toList.imp ne_of_beq_false)


theorem hashset_insert_remaining_lt {α} [FiniteHashable α] {s: Std.HashSet α} {a: α} (h: a ∉ s):
    cardinal α - (s.insert a).size < cardinal α - s.size :=
  have sins: (s.insert a).size = s.size + 1 := Std.HashSet.size_insert.trans (dif_neg h)
  have eq: (s.insert a).size - 1 = s.size := Nat.sub_eq_of_eq_add sins
  have pos: (s.insert a).size ≠ 0 := sins ▸ Nat.add_one_ne_zero _
  eq ▸ Nat.sub_lt_sub_left
    (Nat.sub_one_lt_of_le (Nat.zero_lt_of_ne_zero pos) hashset_size_le)
    (Nat.sub_one_lt pos)


theorem hashmap_size_le {α β} [FiniteHashable α] {s: Std.HashMap α β}: s.size ≤ cardinal α :=
  Std.HashMap.length_keys (α := α) ▸ finite s.keys (Std.HashMap.distinct_keys.imp ne_of_beq_false)


theorem hashmap_insert_remaining_lt {α β} [FiniteHashable α]
  {s: Std.HashMap α β} {a: α} (h: a ∉ s) {b: β}:
    cardinal α - (s.insert a b).size < cardinal α - s.size :=
  have sins: (s.insert a b).size = s.size + 1 := Std.HashMap.size_insert.trans (dif_neg h)
  have eq: (s.insert a b).size - 1 = s.size := Nat.sub_eq_of_eq_add sins
  have pos: (s.insert a b).size ≠ 0 := sins ▸ Nat.add_one_ne_zero _
  eq ▸ Nat.sub_lt_sub_left
    (Nat.sub_one_lt_of_le (Nat.zero_lt_of_ne_zero pos) hashmap_size_le)
    (Nat.sub_one_lt pos)


end FiniteHashable
end
