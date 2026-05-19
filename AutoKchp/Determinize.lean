/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.NatNFA
public import AutoKchp.CDFA
import AutoKchp.Internal.HeapSort
import AutoKchp.Internal.Counting
import AutoKchp.Internal.Util


def powerInitial {a: Nat} (r: NatNFA a): Array (Fin r.n) :=
  canonicalize (Fin.foldl r.n (fun acc q => if r.i q then acc.push q else acc) #[])


def powerDelta {a: Nat} (r: NatNFA a) (p: Array (Fin r.n)) (b: Fin a):
    Array (Fin r.n) :=
  canonicalize (p.foldl (fun acc q => acc.append (r.δ q b)) #[])


def powerFinal {a: Nat} (r: NatNFA a): Array (Fin r.n) → Bool :=
  fun v => v.any (fun p => r.f p)


theorem mem_powerInitial {a: Nat} {r: NatNFA a} {p: Fin r.n}:
    p ∈ powerInitial r ↔ r.i p :=
  mem_canonicalize.trans (
    let motive (acc: Array (Fin r.n)) (j: Nat) := p ∈ acc ↔ p < j ∧ r.i p
    have ind: motive (Fin.foldl r.n (fun acc q => if r.i q then acc.push q else acc) #[]) r.n :=
      Fin.foldl_induction motive
        ⟨fun mem => False.elim (Array.not_mem_empty p mem),
          fun ⟨lt, _⟩ => False.elim (Nat.not_lt_zero p lt)⟩
        fun _ i hrec => iteInduction (motive := fun w => motive w (i + 1))
          (fun pos => Array.mem_push.trans ⟨
            fun
              | .inl mem => have ⟨lt, pos⟩ := hrec.mp mem; ⟨Nat.lt_succ_of_lt lt, pos⟩
              | .inr eq => ⟨eq ▸ Nat.lt_succ_self i, eq ▸ pos⟩,
            fun ⟨lt, pos2⟩ => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt) with
              | .inl lt => Or.inl (hrec.mpr ⟨lt, pos2⟩)
              | .inr eq => Or.inr (Fin.eq_of_val_eq eq)
          ⟩)
          (fun neg => ⟨
            fun mem => have ⟨lt, pos⟩ := hrec.mp mem; ⟨Nat.lt_succ_of_lt lt, pos⟩,
            fun ⟨lt, pos⟩ => hrec.mpr ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ lt)
              (fun eq => neg ((Fin.eq_of_val_eq eq) ▸ pos)), pos⟩
          ⟩)
    ⟨And.right ∘ ind.mp, ind.mpr ∘ (fun pos => ⟨p.isLt, pos⟩)⟩
  )


theorem mem_powerDelta {a: Nat} {r: NatNFA a} {v: Array (Fin r.n)} {b: Fin a} {p: Fin r.n}:
    p ∈ powerDelta r v b ↔ ∃ q: Fin r.n, q ∈ v ∧ p ∈ r.δ q b :=
  mem_canonicalize.trans (
    let motive (i: Nat) (acc: Array (Fin r.n)) := p ∈ acc ↔ ∃ j: Fin v.size, j < i ∧ p ∈ r.δ v[j] b
    have ind: motive v.size (v.foldl (fun acc q => acc.append (r.δ q b)) #[]) :=
      Array.foldl_induction motive
        ⟨fun mem => False.elim (Array.not_mem_empty p mem),
          fun ⟨_, lt, _⟩ => False.elim (Nat.not_lt_zero _ lt)⟩
        (fun i acc hrec => Array.mem_append.trans ⟨
          fun
            | .inl mem => have ⟨j, hj, mem2⟩ := hrec.mp mem; ⟨j, Nat.lt_succ_of_lt hj, mem2⟩
            | .inr mem => ⟨i, Nat.lt_succ_self i, mem⟩,
          fun ⟨j, hj, mem⟩ => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
            | .inl lt => Or.inl (hrec.mpr ⟨j, lt, mem⟩)
            | .inr eq => Or.inr ((Fin.eq_of_val_eq eq) ▸ mem)
        ⟩)
    ind.trans ⟨
      fun ⟨j, _, mem⟩ => ⟨v[j], Array.getElem_mem _, mem⟩,
      fun ⟨q, mem1, mem2⟩ => have ⟨j, hj, eq⟩ := Array.getElem_of_mem mem1
        ⟨⟨j, hj⟩, hj, eq ▸ mem2⟩
    ⟩
  )


theorem powerFinal_correct {a: Nat} {r: NatNFA a} {v: Array (Fin r.n)}:
    powerFinal r v = true ↔ ∃ p: Fin r.n, p ∈ v ∧ r.f p :=
  Array.any_eq_true'


def allSubsets: (n: Nat) → List (Array Nat)
  | 0 => [#[]]
  | n + 1 => allSubsets n ++ (allSubsets n).map (fun s => s.push n)


theorem allSubsets_lt: {n: Nat} → ∀ v: Array Nat, v ∈ (allSubsets n) → ∀ i: Nat, i ∈ v → i < n
  | 0 => fun _ mem i imem => False.elim (Array.not_mem_empty i ((List.mem_singleton.mp mem) ▸ imem))
  | n + 1 => fun v mem => match List.mem_append.mp mem with
    | .inl mem => fun i imem => Nat.lt_succ_of_lt (allSubsets_lt v mem i imem)
    | .inr mem =>
      have ⟨u, umem, eq⟩ := List.mem_map.mp mem
      eq ▸ (fun i imem =>
        match Array.mem_push.mp imem with
        | .inl imem => Nat.lt_succ_of_lt (allSubsets_lt u umem i imem)
        | .inr eq => eq ▸ Nat.lt_succ_self n
      )


theorem allSubsets_sorted: {n: Nat} → ∀ v: Array Nat, v ∈ (allSubsets n) → v.toList.Pairwise (· < ·)
  | 0 => fun _ mem => (List.mem_singleton.mp mem) ▸ List.Pairwise.nil
  | n + 1 => fun v mem => match List.mem_append.mp mem with
    | .inl mem => allSubsets_sorted v mem
    | .inr mem =>
      have ⟨u, umem, eq⟩ := List.mem_map.mp mem
      eq ▸ (Array.toList_push ▸ List.pairwise_append.mpr ⟨
        allSubsets_sorted u umem,
        List.pairwise_singleton (· < ·) n,
        fun i imem _ jmem => (List.mem_singleton.mp jmem) ▸ allSubsets_lt u umem i
          (Array.mem_toList_iff.mp imem)
      ⟩)


theorem allSubsets_exhaustive: {n: Nat} → ∀ v: Array Nat,
    v.toList.Pairwise (· < ·) → (∀ i: Nat, i ∈ v → i < n) → v ∈ (allSubsets n)
  | 0 => fun v _ h => List.mem_singleton.mpr (Array.eq_empty_iff_forall_not_mem.mpr (fun i hi =>
    Nat.not_lt_zero i (h i hi)))
  | n + 1 => fun v hv hv2 => List.mem_append.mpr (
      if eq: v.back? = some n then
        have ⟨u, equ⟩ := Array.back?_eq_some_iff.mp eq;
        have ⟨hu, _, hu2⟩ := List.pairwise_append.mp (Array.toList_push ▸ equ ▸ hv)
        have umem := allSubsets_exhaustive u hu (fun i hi =>
          hu2 i (Array.mem_toList_iff.mpr hi) n (List.mem_singleton_self n))
        Or.inr (List.mem_map.mpr ⟨u, umem, equ.symm⟩)
      else
        Or.inl (allSubsets_exhaustive v hv (fun i hi => match Nat.lt_or_ge i n with
          | .inl lt => lt
          | .inr ge =>
            have ieq: i = n := Nat.le_antisymm (Nat.le_of_lt_succ (hv2 i hi)) ge
            have ⟨j, hj, eqj⟩ := Array.getElem_of_mem hi
            if eqb: j = v.size - 1 then
              False.elim (eq (Array.back?_eq_getElem? ▸ (Array.getElem?_eq_getElem _ ▸ (congrArg some
                ((eqj.trans ieq).symm.trans (getElem_congr_idx eqb)))).symm))
            else
              have hsj: j + 1 < v.size := Nat.lt_of_le_of_ne
                (Nat.le_of_lt_succ (Nat.add_lt_add_right hj 1))
                (fun eq2 => eqb (Nat.eq_sub_of_add_eq eq2))
              Nat.lt_of_lt_of_le
                (eqj ▸ Array.getElem_toList hj ▸ Array.getElem_toList hsj ▸
                  List.pairwise_iff_getElem.mp hv j (j + 1) hj hsj (Nat.lt_succ_self j))
                (Nat.le_of_lt_succ (hv2 v[j + 1] (Array.getElem_mem hsj)))
        ))
    )


theorem allSubsets_length: {n: Nat} → (allSubsets n).length = 2 ^ n
  | 0 => rfl
  | n + 1 =>
    have lmap: ((allSubsets n).map (fun s => s.push n)).length = 2 ^ n :=
      (List.length_map _).symm ▸ allSubsets_length (n := n);
    List.length_append.trans (Eq.trans (allSubsets_length.symm ▸ congrArg (2 ^ n + ·) lmap)
      (Nat.two_pow_succ n).symm)


def allSubsetsAttached (n: Nat): List {v: Array (Fin n) // v.toList.Pairwise (· < ·)} :=
  (allSubsets n).attach.map (fun ⟨v, mem⟩ => ⟨
    v.attach.map (fun ⟨i, imem⟩ => ⟨i, allSubsets_lt v mem i imem⟩),
    Array.toList_map ▸ List.pairwise_map.mpr (
      List.pairwise_iff_getElem.mpr (fun i j hi hj hij =>
        have len1: v.attach.toList.length = v.size :=
          Array.length_toList.trans Array.size_attach
        have len: v.attach.toList.length = v.toList.length :=
          len1.trans Array.length_toList.symm
        have lt := List.pairwise_iff_getElem.mp (allSubsets_sorted v mem) i j (len ▸ hi) (len ▸ hj) hij
        have lt: v[i] < v[j] := Array.getElem_toList _ ▸ Array.getElem_toList _ ▸ lt
        have eqi: v.attach.toList[i].val = v[i] := congrArg Subtype.val (Array.getElem_attach _)
        have eqj: v.attach.toList[j].val = v[j] := congrArg Subtype.val (Array.getElem_attach _)
        have concl_lt: v.attach.toList[i].val < v.attach.toList[j].val := eqi ▸ (eqj ▸ lt)
        ⟨Nat.le_of_lt concl_lt, Fin.ne_of_val_ne (Nat.ne_of_lt concl_lt)⟩
      )
    )⟩)


theorem allSubsetsAttached_exhaustive {n: Nat}:
    ∀ v: {v: Array (Fin n) // v.toList.Pairwise (· < ·)}, v ∈ allSubsetsAttached n :=
  fun ⟨v, hv⟩ =>
    let v2 := v.map Fin.val
    have mem: v2 ∈ allSubsets n := allSubsets_exhaustive v2
      (Array.toList_map ▸ List.pairwise_map.mpr (List.Pairwise.imp (fun lt =>
        Nat.lt_of_le_of_ne lt.left (Fin.val_ne_of_ne lt.right)) hv))
      (fun _ hi => have ⟨⟨_, lt⟩, _, eq⟩ := Array.mem_map.mp hi; eq ▸ lt)
    List.mem_map.mpr ⟨⟨v2, mem⟩, List.mem_attach _ _, Subtype.ext
      (Array.map_attach_eq_pmap.trans
        ((Array.pmap_map fun _ => id).trans (Array.pmap_eq_self.mpr fun _ _ => rfl)))
    ⟩


theorem allSubsetsAttached_length {n: Nat}:
    (allSubsetsAttached n).length = 2 ^ n :=
  (List.length_map _).trans (List.length_attach.trans allSubsets_length)


theorem card_subsets {n: Nat} {l: List {v: Array (Fin n) // v.toList.Pairwise (· < ·)}}:
    l.card ≤ 2 ^ n :=
  Nat.le_trans (List.card_mono (
    fun v _ => allSubsetsAttached_exhaustive v
  )) (allSubsetsAttached_length ▸ List.card_le_length)


instance {n: Nat}: FiniteHashable { v: Array (Fin n) // v.toList.Pairwise (· < ·) } := {
  cardinal := 2 ^ n
  finite := fun _ hl => List.card_eq_length_of_nodup hl ▸ card_subsets
}


def constructPower {a: Nat} (r: NatNFA a): CDFA a := {
  σ := { v: Array (Fin r.n) // v.toList.Pairwise (· < ·) }
  finite := inferInstance
  δ := fun p b => ⟨powerDelta r p.val b, canonicalize_sorted⟩
  i := ⟨powerInitial r, canonicalize_sorted⟩
  f := fun p => powerFinal r p.val
}


theorem constructPower_path {a: Nat} {r: NatNFA a} {f: Fin r.n} {v: Array (Fin r.n)}
  (hv: v.toList.Pairwise (· < ·)):
    {l: List (Fin a)} → (∃ i: Fin r.n, i ∈ v ∧ r.path i f l) ↔ f ∈ ((constructPower r).advanceFrom ⟨v, hv⟩ l).val
  | [] => ⟨
    fun ⟨_, mem, eq⟩ => eq ▸ mem,
    fun mem => ⟨f, mem, rfl⟩,
  ⟩
  | b::_ => Iff.trans
    ⟨
      fun ⟨i, mem, ⟨i2, mem2, path⟩⟩ =>
        ⟨i2, mem_powerDelta.mpr ⟨i, mem, mem2⟩, path⟩,
      fun ⟨i2, mem2, path⟩ => have ⟨i, mem, del⟩ := mem_powerDelta.mp mem2
        ⟨i, mem, ⟨i2, del, path⟩⟩,
    ⟩
    (constructPower_path ((constructPower r).δ ⟨v, hv⟩ b).property)


theorem constructPower_path_initial {a: Nat} {r: NatNFA a} {f: Fin r.n} {l: List (Fin a)}:
    (∃ i: Fin r.n, r.i i ∧ r.path i f l) ↔ f ∈ ((constructPower r).advance l).val :=
  Iff.trans ⟨
    fun ⟨i, pos, path⟩ => ⟨i, mem_powerInitial.mpr pos, path⟩,
    fun ⟨i, mem, path⟩ => ⟨i, mem_powerInitial.mp mem, path⟩
  ⟩ (constructPower_path (constructPower r).i.property)


theorem constructPower_accepts {a: Nat} {r: NatNFA a} {l: List (Fin a)}:
    r.accepts l ↔ (constructPower r).accepts l = true :=
  ⟨
    fun ⟨i, f, ⟨path, hi, hf⟩⟩ => powerFinal_correct.mpr
      ⟨f, (constructPower_path_initial.mp ⟨i, hi, path⟩), hf⟩,
    fun h => have ⟨f, mem, hf⟩ := powerFinal_correct.mp h
      have ⟨i, hi, path⟩ := constructPower_path_initial.mpr mem
      ⟨i, f, ⟨path, hi, hf⟩⟩
  ⟩


public section
namespace NatNFA


structure DeterminizationResult {a: Nat} (r: NatNFA a) where
  determinized: CDFA a
  correct: ∀ l: List (Fin a), determinized.accepts l = true ↔ r.accepts l


def determinize {a: Nat} (r: NatNFA a): DeterminizationResult r := {
  determinized := constructPower r
  correct := fun _ => constructPower_accepts.symm
}


end NatNFA
end
