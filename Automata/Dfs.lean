import Automata.NatCDFA


def Vector.cNone {α} {n: Nat} (v: Vector (Option α) n) := v.countP Option.isNone


theorem Vector.cNone_set {α} {n: Nat} {v: Vector (Option α) n} {i: Fin n} {x: α}
  (h: v.get i = none):
    (v.set i x).cNone + 1 = v.cNone :=
  have cond: v[i.val].isNone = true := Option.isNone_iff_eq_none.mpr h
  have le: v.countP Option.isNone ≥ 1 := Nat.one_le_of_lt (Vector.countP_pos_iff.mpr
    ⟨v.get i, Vector.getElem_mem _, Option.isNone_iff_eq_none.mpr h⟩)
  (congrArg (· + 1) (Vector.countP_set i.isLt)).trans (
    ite_cond_eq_true _ _ (eq_true cond) ▸ Nat.sub_add_comm le ▸
    (Nat.sub_add_cancel (Nat.le_add_right_of_le le)).symm ▸ rfl)


def dfsFindMorphism {a: Nat} (r s: NatCDFA a) (p: Fin r.n) (q: Fin s.n) (asgn: Vector (Option (Fin s.n)) r.n):
    Option { v: Vector (Option (Fin s.n)) r.n // v.cNone ≤ asgn.cNone } :=
  match h: asgn.get p with
    | none => (Fin.foldlM a (fun (acc: { v: Vector (Option (Fin s.n)) r.n // v.cNone + 1 ≤ asgn.cNone }) b => (
        (dfsFindMorphism r s (r.δ p b) (s.δ q b) acc.val).map
          (fun acc2 => ⟨acc2.val, Nat.le_trans (Nat.add_le_add_right acc2.property 1) acc.property⟩)
      )) ⟨(asgn.set p (some q)), Nat.le_of_eq (Vector.cNone_set h)⟩).map
      (fun acc3 => ⟨acc3.val, Nat.le_of_succ_le acc3.property⟩)
    | some q' => if q' = q then some ⟨asgn, Nat.le_refl _⟩ else none
  termination_by asgn.countP Option.isNone
  decreasing_by exact Nat.lt_of_succ_le acc.property
