/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

import AutoKchp.Internal.Util


def warshallSet {n: Nat} (v: Vector (Vector Bool n) n) (i j: Fin n):
    Vector (Vector Bool n) n :=
  v.modify i (fun v2 => v2.set j true)


theorem warshallSet_correct {n: Nat} {v: Vector (Vector Bool n) n} {i j: Fin n}:
    ∀ a b: Fin n, ((warshallSet v i j).get a).get b ↔ (v.get a).get b ∨ i = a ∧ j = b :=
  fun a b =>
    if eqi: i = a then
      have c: ((v.get a).set j true).get b ↔ (v.get a).get b ∨ i = a ∧ j = b :=
        if eqj: j = b then
          ⟨fun _ => Or.inr ⟨eqi, eqj⟩, fun _ => eqj ▸ Vector.get_set_self⟩
        else
         (Vector.get_set_of_ne eqj).symm ▸
          ⟨Or.inl, fun h => h.resolve_right (fun ⟨_, eq⟩ => eqj eq)⟩
      have concl: ((v.modify i fun v => v.set j true).get a).get b
          ↔ (v.get a).get b ∨ i = a ∧ j = b :=
        Iff.trans (eqi.symm ▸ Vector.get_modify_self ▸ Iff.refl _) c
      concl
    else
      (Vector.get_modify_of_ne eqi).symm ▸
        ⟨Or.inl, fun h => h.resolve_right (fun ⟨eq, _⟩ => eqi eq)⟩


def warshallSubstep {n: Nat} (v: Vector (Vector Bool n) n) (k i: Fin n):
    Vector (Vector Bool n) n :=
  Fin.foldl n (fun acc j =>
    if (acc.get k).get j then
      warshallSet acc i j
    else
      acc
  ) v


theorem warshallSubstep_correct {n: Nat} {v: Vector (Vector Bool n) n} {k i: Fin n}:
    ∀ a b: Fin n, ((warshallSubstep v k i).get a).get b ↔ (v.get a).get b ∨
      i = a ∧ (v.get k).get b :=
  let motive (acc: Vector (Vector Bool n) n) (m: Nat): Prop :=
    ∀ a b: Fin n, (acc.get a).get b ↔ (v.get a).get b ∨ i = a ∧ b < m ∧ (v.get k).get b
  have ind: motive (warshallSubstep v k i) n := Fin.foldl_induction motive
    (fun _ b => ⟨Or.inl, fun h => h.resolve_right (fun ⟨_, lt, _⟩ => Nat.not_lt_zero b lt)⟩)
    (fun _ m hrec => iteInduction (motive := fun acc => motive acc _)
      (fun pos a b => (warshallSet_correct a b).trans ⟨
        fun
        | .inl h => match (hrec a b).mp h with
          | .inl h => .inl h
          | .inr ⟨hi, hj , h2⟩ => .inr ⟨hi, Nat.lt_succ_of_lt hj, h2⟩
        | .inr ⟨eqi, eqj⟩ => .inr ⟨eqi, eqj ▸ Nat.lt_succ_self _,
            eqj ▸ ((hrec k m).mp pos).resolve_right (fun ⟨_, lt, _⟩ => Nat.lt_irrefl _ lt)⟩,
        fun
        | .inl h => .inl ((hrec a b).mpr (Or.inl h))
        | .inr ⟨hi, hj, h2⟩ => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
          | .inl lt => .inl ((hrec a b).mpr (Or.inr ⟨hi, lt, h2⟩))
          | .inr eq => .inr ⟨hi, Fin.eq_of_val_eq eq.symm⟩
      ⟩)
      (fun neg a b => (hrec a b).trans ⟨
        fun | .inl h => .inl h | .inr ⟨hi, hj, h2⟩ => .inr ⟨hi, Nat.lt_succ_of_lt hj, h2⟩,
        fun | .inl h => .inl h | .inr ⟨hi, hj, h2⟩ => .inr ⟨hi,
          (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)).resolve_right
          (fun eq => neg ((Fin.eq_of_val_eq eq) ▸ ((hrec k b).mpr (Or.inl h2)))), h2⟩
      ⟩)
    )
  fun a b => (ind a b).trans ⟨
    fun | .inl h => .inl h | .inr ⟨hi, _, h2⟩ => .inr ⟨hi, h2⟩,
    fun | .inl h => .inl h | .inr ⟨hi, h2⟩ => .inr ⟨hi, b.isLt, h2⟩
  ⟩


def warshallStep {n: Nat} (v: Vector (Vector Bool n) n) (k: Fin n):
    Vector (Vector Bool n) n :=
  Fin.foldl n (fun acc i =>
    if (acc.get i).get k then
      warshallSubstep acc k i
    else acc
  ) v


theorem warshallStep_correct {n: Nat} {v: Vector (Vector Bool n) n} {k: Fin n}:
    ∀ i j: Fin n, ((warshallStep v k).get i).get j
      ↔ (v.get i).get j ∨ ((v.get i).get k ∧ (v.get k).get j) :=
  let motive (acc: Vector (Vector Bool n) n) (a: Nat): Prop := ∀ i j: Fin n,
    ((acc.get i).get j ↔ (v.get i).get j ∨ i < a ∧ (v.get i).get k ∧ (v.get k).get j)
  have ind: motive (warshallStep v k) n := Fin.foldl_induction motive
    (fun i _ => ⟨Or.inl, fun h => h.resolve_right (fun ⟨lt, _, _⟩ => Nat.not_lt_zero i lt)⟩)
    (fun _ a hrec =>
      iteInduction (motive := fun acc => motive acc _)
        (fun pos i j =>
          (warshallSubstep_correct i j).trans ⟨
            fun
            | .inl h => match (hrec i j).mp h with
              | .inl h => .inl h
              | .inr ⟨hi, h1, h2⟩ => .inr ⟨Nat.lt_succ_of_lt hi, h1, h2⟩
            | .inr ⟨eqi, h⟩ => .inr ⟨eqi ▸ Nat.lt_succ_self _,
                eqi ▸ ((hrec a k).mp pos).resolve_right (fun ⟨lt, _, _⟩ => Nat.lt_irrefl a lt),
                match (hrec k j).mp h with | .inl h => h | .inr ⟨_, _, h⟩ => h
              ⟩,
            fun
            | .inl h => .inl ((hrec i j).mpr (Or.inl h))
            | .inr ⟨hi, h1, h2⟩ => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
              | .inl lt => .inl ((hrec i j).mpr (Or.inr ⟨lt, h1, h2⟩))
              | .inr eq => .inr ⟨Fin.eq_of_val_eq eq.symm, (hrec k j).mpr (Or.inl h2)⟩
          ⟩
        )
        (fun neg i j => (hrec i j).trans ⟨
          fun | .inl h => .inl h | .inr ⟨hi, h1, h2⟩ => .inr ⟨Nat.lt_succ_of_lt hi, h1, h2⟩,
          fun | .inl h => .inl h | .inr ⟨hi, h1, h2⟩ => .inr ⟨
            (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)).resolve_right (fun eq =>
              neg ((Fin.eq_of_val_eq eq) ▸ ((hrec i k).mpr (Or.inl h1)))),
            h1, h2
          ⟩
        ⟩)
    )
  fun i j => (ind i j).trans ⟨
    fun | .inl h => .inl h | .inr ⟨_, h1, h2⟩ => .inr ⟨h1, h2⟩,
    fun | .inl h => .inl h | .inr ⟨h1, h2⟩ => .inr ⟨i.isLt, h1, h2⟩
  ⟩


public def warshall {n: Nat} (v: Vector (Vector Bool n) n):
    Vector (Vector Bool n) n :=
  Fin.foldl n (fun acc k => warshallStep acc k) v


inductive warshallPath {n: Nat} (v: Vector (Vector Bool n) n) (k: Nat): Fin n → Fin n → Prop where
  | base {i j: Fin n}: (v.get i).get j → warshallPath v k i j
  | trans {a b c: Fin n}: b < k → warshallPath v k a b → warshallPath v k b c → warshallPath v k a c


theorem warshallPath_zero {n: Nat} {v: Vector (Vector Bool n) n} {i j: Fin n}:
    warshallPath v 0 i j ↔ (v.get i).get j :=
  ⟨
    fun
    | warshallPath.base h => h
    | warshallPath.trans lt _ _ => False.elim (Nat.not_lt_zero _ lt),
    fun h => warshallPath.base h
  ⟩


theorem warshallPath_succ {n: Nat} {v: Vector (Vector Bool n) n} {k: Nat} {i j: Fin n}:
    warshallPath v k i j → warshallPath v (k + 1) i j
  | warshallPath.base h => warshallPath.base h
  | warshallPath.trans lt h1 h2 => warshallPath.trans (Nat.lt_succ_of_lt lt)
    (warshallPath_succ h1) (warshallPath_succ h2)


theorem warshallPath_decompose {n: Nat} {v: Vector (Vector Bool n) n} {k: Fin n} {i j: Fin n}:
    warshallPath v (k + 1) i j → warshallPath v k i j ∨
      warshallPath v k i k ∧ warshallPath v k k j
  | warshallPath.base h => Or.inl (warshallPath.base h)
  | warshallPath.trans (b := b) lt h1 h2 => if eq: b = k then
      Or.inr ⟨
        match warshallPath_decompose h1 with | .inl h1 => eq ▸ h1 | .inr ⟨h1, _⟩ => h1,
        match warshallPath_decompose h2 with | .inl h2 => eq ▸ h2 | .inr ⟨_, h2⟩ => h2
      ⟩
    else
      have lt: b < k := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ lt) (Fin.val_ne_of_ne eq)
      match warshallPath_decompose h1 with
      | .inl h1 => match warshallPath_decompose h2 with
        | .inl h2 => Or.inl (warshallPath.trans lt h1 h2)
        | .inr ⟨h21, h22⟩ => Or.inr ⟨warshallPath.trans lt h1 h21, h22⟩
      | .inr ⟨h11, h12⟩ => match warshallPath_decompose h2 with
        | .inl h2 => Or.inr ⟨h11, warshallPath.trans lt h12 h2⟩
        | .inr ⟨_, h22⟩ => Or.inr ⟨h11, h22⟩


theorem warshallPath_decompose' {n: Nat} {v: Vector (Vector Bool n) n} {k: Fin n} {i j: Fin n}:
    warshallPath v (k + 1) i j ↔ warshallPath v k i j ∨
      warshallPath v k i k ∧ warshallPath v k k j :=
  ⟨warshallPath_decompose, fun
    | .inl h => warshallPath_succ h
    | .inr ⟨h1, h2⟩ => warshallPath.trans (Nat.lt_succ_self k)
      (warshallPath_succ h1) (warshallPath_succ h2)⟩


public inductive transitivePath {n: Nat} (v: Vector (Vector Bool n) n): Fin n → Fin n → Prop where
  | base {i j: Fin n}: (v.get i).get j → transitivePath v i j
  | trans {a b c: Fin n}: transitivePath v a b → transitivePath v b c → transitivePath v a c


theorem warshallPath_of_transitivePath {n: Nat} {v: Vector (Vector Bool n) n} {i j: Fin n}:
    transitivePath v i j → warshallPath v n i j
  | transitivePath.base h => warshallPath.base h
  | transitivePath.trans (b := b) h1 h2 => warshallPath.trans b.isLt
    (warshallPath_of_transitivePath h1) (warshallPath_of_transitivePath h2)


theorem transitivePath_of_warshallPath {n: Nat} {v: Vector (Vector Bool n) n} {k: Nat} {i j: Fin n}:
    warshallPath v k i j → transitivePath v i j
  | warshallPath.base h => transitivePath.base h
  | warshallPath.trans _ h1 h2 => transitivePath.trans
    (transitivePath_of_warshallPath h1) (transitivePath_of_warshallPath h2)


theorem warshallPath_iff_transitivePath {n: Nat} {v: Vector (Vector Bool n) n} {i j: Fin n}:
    warshallPath v n i j ↔ transitivePath v i j :=
  ⟨transitivePath_of_warshallPath, warshallPath_of_transitivePath⟩


public theorem warshall_correct {n: Nat} {v: Vector (Vector Bool n) n}:
    ∀ i j: Fin n, ((warshall v).get i).get j ↔ transitivePath v i j :=
  let motive (acc: Vector (Vector Bool n) n) (k: Nat): Prop :=
    ∀ i j: Fin n, (acc.get i).get j ↔ warshallPath v k i j
  have ind: motive (warshall v) n := Fin.foldl_induction motive
    (fun _ _ => warshallPath_zero.symm)
    (fun _ k hrec i j => ((warshallStep_correct i j).trans (
      or_congr (hrec i j) (and_congr (hrec i k) (hrec k j))
    )).trans warshallPath_decompose'.symm)
  fun i j => (ind i j).trans warshallPath_iff_transitivePath
