/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.NatCDFA
import AutoKchp.Internal.Util

/-
DFS to find a "state morphism" (which does not necessarily map terminal states to terminal states)
-/
abbrev DFSTable {a: Nat} (r s: NatCDFA a) := Vector (Option (Fin s.n × List (Fin a))) r.n


abbrev DFSError (a: Nat) := List (Fin a) × List (Fin a)


abbrev DFSResult {a: Nat} (r s: NatCDFA a) := Except (DFSError a) (DFSTable r s)


def dfsFindMorphismFrom {a: Nat} (r s: NatCDFA a) (p: Fin r.n) (q: Fin s.n)
  (l: List (Fin a)) (asgn: DFSTable r s):
    Nat → DFSResult r s
  | 0 => Except.error ([], []) --Should be unreachable with enough fuel
  | fuel + 1 =>
    match asgn.get p with
    | none => Fin.foldlM a
      (fun acc b => dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) (b::l) acc fuel)
      (asgn.set p (some (q, l)))
    | some (q', l') => if q' = q then Except.ok asgn else Except.error (l.reverse, l'.reverse)


theorem dfsFindMorphismFrom_preserves_some {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {l: List (Fin a)} {asgn: DFSTable r s} {i: Fin r.n} {v: Fin s.n × List (Fin a)} (h: asgn.get i = some v):
    {fuel: Nat} → (dfsFindMorphismFrom r s p q l asgn fuel).allP (fun w => w.get i = some v)
  | 0 => True.intro
  | fuel + 1 =>
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        Fin.foldlM_induction (fun (w: Except _ _) _ => w.allP _)
          (have ne: p ≠ i := fun eq2 => Option.some_ne_none v (h.symm.trans (eq2 ▸ eq))
            have concl: (asgn.set p (some (q, l))).get i = some v :=
              (Vector.get_set_of_ne ne).trans h
            Except.pure_def ▸ concl)
          (fun acc b hrec =>
            match acc with
            | Except.error _ => True.intro
            | Except.ok acc => dfsFindMorphismFrom_preserves_some hrec)
    | some q' => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Except _ _ => w.allP _)
          (fun _ => h) (fun _ => True.intro)


theorem dfsFindMorphismFrom_step {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {l: List (Fin a)} {asgn: DFSTable r s}:
    {fuel: Nat} → (dfsFindMorphismFrom r s p q l asgn fuel).allP (fun w => ∃ u: List (Fin a), w.get p = some (q, u))
  | 0 => True.intro
  | _ + 1 =>
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        Fin.foldlM_induction (fun (w: Except _ _) _ => w.allP _)
          (Except.pure_def ▸ ⟨l, Vector.get_set_self⟩)
          (fun acc _ hrec =>
            match acc with
            | Except.error _ => True.intro
            | Except.ok _ =>
              have ⟨u, hu⟩ := hrec
              Except.allP_mp (dfsFindMorphismFrom_preserves_some hu) (fun _ hu2 => ⟨u, hu2⟩)
          )
    | some (_, l') => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Except _ _ => w.allP _)
          (fun eq2 => ⟨l', eq2 ▸ eq⟩) (fun _ => True.intro)


def okInvariant {a: Nat} (r s: NatCDFA a)
  (grey: List (Fin r.n)) (acc: DFSTable r s): Prop :=
    ∀ p: Fin r.n, p ∉ grey → (acc.get p).allP (fun (q, _) => ∀ b: Fin a, ∃ u: List (Fin a),
      acc.get (r.δ p b) = some (s.δ q b, u)
    )


--Big ugly theorem (the annoying part is handling partially explored - grey - nodes)
theorem dfsFindMorphismFrom_ok_correct {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {l: List (Fin a)} {asgn: DFSTable r s} (grey: List (Fin r.n))
  (hm: okInvariant r s grey asgn):
    {fuel: Nat} → (dfsFindMorphismFrom r s p q l asgn fuel).allP (okInvariant r s grey)
  | 0 => True.intro
  | fuel + 1 => match eq: asgn.get p with
    | none =>
      let motive (acc: DFSResult r s) (c: Nat): Prop := acc.allP (fun acc2 =>
          okInvariant r s (p::grey) acc2
          ∧ (∀ b: Fin a, b.val < c → ∃ u: List (Fin a), acc2.get (r.δ p b) = some (s.δ q b, u))
          ∧ (∃ u: List (Fin a), acc2.get p = some (q, u))
        )
      have ind: motive (Fin.foldlM a
          (fun acc b => dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) (b::l) acc fuel)
          (asgn.set p (some (q, l)))) a :=
        Fin.foldlM_induction motive
          (Except.pure_def ▸ ⟨
            fun i hi =>
                have ne: p ≠ i := fun eq2 => hi (eq2 ▸ List.mem_cons_self)
                have nmem: i ∉ grey := fun mem => hi (List.mem_cons_of_mem _ mem)
                (Vector.get_set_of_ne ne).symm ▸ (Option.allP_mp (hm i nmem) (fun ⟨j, u⟩ hj b =>
                  have ⟨uj, huj⟩ := hj b
                  have ne2: p ≠ r.δ i b := fun eq2 => (Option.some_ne_none (s.δ j b, uj))
                    (huj.symm.trans (eq2 ▸ eq))
                  (Vector.get_set_of_ne ne2).symm ▸ hj b)),
            fun b hb => False.elim (Nat.not_lt_zero b hb),
            ⟨l, Vector.get_set_self⟩
          ⟩)
          (fun acc b hrec => match acc with
              | Except.error _ => True.intro
              | Except.ok acc => (
                  have prev: (dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) (b::l) acc fuel).allP
                      (fun acc2 => ∀ c: Fin a, c.val < b → ∃ u: List (Fin a), acc2.get (r.δ p c) = some (s.δ q c, u)) :=
                    Except.allP_forall.mp (fun c => Except.allP_imp.mp (fun hc =>
                      have ⟨u, hu⟩ := hrec.right.left c hc
                      Except.allP_mp (dfsFindMorphismFrom_preserves_some hu) (fun acc2 hacc2 => ⟨u, hacc2⟩)
                    ))
                  Except.allP_mp (Except.allP_and.mp ⟨
                    dfsFindMorphismFrom_ok_correct (p::grey) hrec.left,
                    Except.allP_and.mp ⟨
                      prev,
                      Except.allP_and.mp ⟨
                        dfsFindMorphismFrom_step,
                        have ⟨u, hu⟩ := hrec.right.right;
                        Except.allP_mp (dfsFindMorphismFrom_preserves_some hu) (fun _ hu2 => ⟨u, hu2⟩),
                      ⟩
                    ⟩
                  ⟩) (fun acc2 ⟨hrec1, hrec2, hrec3, hrec4⟩ => ⟨
                      hrec1,
                      (fun c hc => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with
                        | .inl lt => hrec2 c lt
                        | .inr eq2 => (Fin.eq_of_val_eq eq2) ▸ hrec3
                      ),
                      hrec4,
                    ⟩
                  )
                )
            )
      dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
          Except.allP_mp ind (fun acc hacc p2 hp2 =>
            if eq2: p2 = p then
              have ⟨u, hu⟩: ∃ u, acc.get p2 = some (q, u) := eq2 ▸ hacc.right.right
              hu ▸ fun b => eq2 ▸ hacc.right.left b b.isLt
            else
              hacc.left p2 (fun mem => match List.mem_cons.mp mem with
                | .inl eq3 => eq2 eq3
                | .inr mem2 => hp2 mem2
              )
          )
    | some q' => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Except _ _ => w.allP _)
          (fun _ =>  hm) (fun _ => True.intro)


theorem dfsFindMorphismFrom_cNone {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {l: List (Fin a)} {asgn: DFSTable r s}:
    {fuel: Nat} → (dfsFindMorphismFrom r s p q l asgn fuel).allP (fun w => w.cNone ≤ asgn.cNone)
  | 0 => True.intro
  | fuel + 1 =>
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        Fin.foldlM_induction (fun (w: Except _ _) _ => w.allP _)
          (Option.pure_def ▸ (Nat.le_of_add_le_add_right (b := 1)
            (Vector.cNone_set eq ▸ Nat.le_succ asgn.cNone)))
          (fun acc b hrec => match acc with
            | Except.error _ => True.intro
            | Except.ok acc =>
              have hrec2: (dfsFindMorphismFrom r s (r.δ p b) (s.δ q b) (b::l) acc fuel).allP
                  (fun w => w.cNone ≤ acc.cNone) := dfsFindMorphismFrom_cNone
              Except.allP_mp hrec2 (fun _ hacc2 => (Nat.le_trans hacc2 hrec))
          )
    | some _ => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        iteInduction (motive := fun w: Except _ _ => w.allP _)
          (fun _ => Nat.le_refl asgn.cNone) (fun _ => True.intro)


def errInvariant {a: Nat} (r s: NatCDFA a) (acc: DFSTable r s): Prop :=
    ∀ p: Fin r.n, (acc.get p).allP (fun (q, u) => r.advance u.reverse = p ∧ s.advance u.reverse = q)


def resultCorrect {a: Nat} {r s: NatCDFA a}: DFSResult r s → Prop
  | Except.ok acc => errInvariant r s acc
  | Except.error (u1, u2) => r.advance u1 = r.advance u2 ∧ s.advance u1 ≠ s.advance u2


theorem dfsFindMorphismFrom_err_correct {a: Nat} {r s: NatCDFA a} {p: Fin r.n} {q: Fin s.n}
  {l: List (Fin a)} {asgn: DFSTable r s} (ht1: errInvariant r s asgn)
  (ht2: p = r.advance l.reverse ∧ q = s.advance l.reverse)
  {fuel: Nat} (hf: fuel > asgn.cNone):
    resultCorrect (dfsFindMorphismFrom r s p q l asgn fuel) :=
  match fuel with
  | 0 => False.elim (Nat.not_lt_zero asgn.cNone hf)
  | fuel + 1 =>
    match eq: asgn.get p with
    | none => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        (Fin.foldlM_induction (fun res _ => resultCorrect res ∧ res.allP (fun z => fuel > z.cNone))
          ⟨Except.pure_def ▸ fun p2 => if eq2: p2 = p then
              congrArg (Vector.get _) eq2 ▸ Vector.get_set_self ▸ ⟨eq2 ▸ ht2.left.symm, ht2.right.symm⟩
            else
              (Vector.get_set_of_ne (Ne.symm eq2)).symm ▸ (ht1 p2),
            Nat.lt_of_add_lt_add_right (Vector.cNone_set eq ▸ hf),
          ⟩
          (fun acc _ hrec => match acc with
              | Except.error _ => hrec
              | Except.ok _ =>
                ⟨
                  dfsFindMorphismFrom_err_correct hrec.left
                    ⟨
                      List.reverse_cons ▸ NatCDFA.advance_concat ▸ ht2.left ▸ rfl,
                      List.reverse_cons ▸ NatCDFA.advance_concat ▸ ht2.right ▸ rfl,
                    ⟩
                    hrec.right,
                  Except.allP_mp dfsFindMorphismFrom_cNone (fun _ hacc2 =>
                    (Nat.lt_of_le_of_lt hacc2 hrec.right))
                ⟩
          )
        ).left
    | some (q', l') => dfsFindMorphismFrom.eq_def r s p q l asgn _ ▸ eq ▸
        iteInduction (motive := resultCorrect)
          (fun _ => ht1)
          (fun ne =>
            have adv: r.advance l'.reverse = p ∧ s.advance l'.reverse = q' := eq.subst (ht1 p)
            ⟨
              ht2.left.symm.trans adv.left.symm,
              fun eq2 => ne (adv.right.symm.trans (eq2.symm.trans ht2.right.symm))
            ⟩
          )

/-
Non-recursive (simpler) version
-/
def dfsFindMorphism {a: Nat} (r s: NatCDFA a): DFSResult r s :=
  dfsFindMorphismFrom r s r.i s.i [] (Vector.replicate r.n none) (r.n + 1)


def allP_of_resultCorrect {a: Nat} {r s: NatCDFA a} {res: DFSResult r s} (h: resultCorrect res):
    res.allP (errInvariant r s) :=
  match res with
  | Except.ok _ => h
  | Except.error _ => True.intro


theorem dfsFindMorphism_ok_correct {a: Nat} {r s: NatCDFA a}:
    (dfsFindMorphism r s).allP (fun acc =>
      (∀ p: Fin r.n, (acc.get p).allP (fun (_, l) => r.advance l.reverse = p))
      ∧ (∀ l: List (Fin a), ∃ u: List (Fin a), acc.get (r.advance l) = some (s.advance l, u))
    ) :=
  Except.allP_mp (Except.allP_and.mp ⟨
    dfsFindMorphismFrom_ok_correct [] (fun p _ => Vector.get_replicate ▸ True.intro),
    Except.allP_and.mp ⟨
      allP_of_resultCorrect (dfsFindMorphismFrom_err_correct
        (fun p => Vector.get_replicate ▸ True.intro)
        ⟨Array.toList_empty ▸ rfl, Array.toList_empty ▸ rfl⟩
        (Nat.lt_succ_of_le Vector.cNone_le)
      ),
      dfsFindMorphismFrom_step
    ⟩
  ⟩) (fun acc ⟨hacc1, hacc2, hacc3⟩ => ⟨
    (fun p => Option.allP_mp (hacc2 p) (fun (q, u) h => h.left)),
    let rec propagate (l: List (Fin a)): ∃ u, acc.get (r.advance l) = some (s.advance l, u) :=
      match List.eq_nil_or_concat l with
      | .inl eq_nil => eq_nil ▸ hacc3
      | .inr ⟨start, b, eq_cat⟩ =>
        have ⟨u, hrec⟩ := propagate start
        have inv: (acc.get (r.advance start)).allP
            (fun (q, _) => ∀ c: Fin a, ∃ u, acc.get (r.δ (r.advance start) c) = some (s.δ q c, u)) :=
          hacc1 (r.advance start) List.not_mem_nil
        have invs: ∀ (c : Fin a), ∃ u, acc.get (r.δ (r.advance start) c) = some (s.δ (s.advance start) c, u) :=
          hrec.subst inv
        have hr: r.advance l = r.δ (r.advance start) b :=
          eq_cat ▸ List.concat_eq_append ▸ NatCDFA.advance_concat
        have hs: s.advance l = s.δ (s.advance start) b :=
          eq_cat ▸ List.concat_eq_append ▸ NatCDFA.advance_concat
        hr ▸ hs ▸ invs b
      termination_by l.length
    propagate
  ⟩)


theorem dfsFindMorphism_err_correct {a: Nat} {r s: NatCDFA a}:
    (dfsFindMorphism r s).allEP (fun (l1, l2) =>
      r.advance l1 = r.advance l2 ∧ s.advance l1 ≠ s.advance l2) :=
  match eq: dfsFindMorphism r s with
  | Except.error (_, _) =>
    have res_correct: resultCorrect (dfsFindMorphism r s) :=
      dfsFindMorphismFrom_err_correct
        (fun _ => Vector.get_replicate ▸ True.intro)
        ⟨Array.toList_empty ▸ rfl, Array.toList_empty ▸ rfl⟩
        (Nat.lt_succ_of_le Vector.cNone_le)
    have concl := eq.subst res_correct; concl
  | Except.ok _ => True.intro


/-
Construction over the previous function to search for a true morphism (or provide a counterexample)
-/
def checkTerminal {a: Nat} (r s: NatCDFA a) (m: DFSTable r s): Except (List (Fin a)) Unit :=
  Fin.foldlM r.n (fun () p =>
    match m.get p with
    | none => Except.ok ()
    | some (q, u) => if s.f q = r.f p then Except.ok () else Except.error u.reverse
  ) ()


def checkTerminal_ok_correct {a: Nat} {r s: NatCDFA a} {m: DFSTable r s}:
    (checkTerminal r s m).allP (fun () => ∀ p: Fin r.n, (m.get p).allP (fun (q, _) => r.f p = s.f q)) :=
  let motive (acc: Except (List (Fin a)) Unit) (i: Nat) :=
    acc.allP (fun () => ∀ p: Fin r.n, p < i → (m.get p).allP (fun (q, _) => r.f p = s.f q))
  have ind: motive (checkTerminal r s m) r.n := Fin.foldlM_induction motive
    (Except.pure_def ▸ fun p hp => False.elim (Nat.not_lt_zero p hp))
    (fun acc i hrec => match acc with
      | Except.error _ => True.intro
      | Except.ok _ => match eq: m.get i with
        | none =>
          have concl: ∀ p: Fin r.n, p < i.val.succ → (m.get p).allP (fun (q, _) => r.f p = s.f q) :=
            fun p hp => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hp) with
              | Or.inl lt => hrec p lt
              | Or.inr eq2 => Fin.eq_of_val_eq eq2 ▸ eq ▸ True.intro
          concl
        | some (_, _) => iteInduction (motive := fun acc => motive acc i.val.succ)
          (fun eq2 =>
            have concl: ∀ p: Fin r.n, p < i.val.succ → (m.get p).allP (fun (q, _) => r.f p = s.f q) :=
            fun p hp => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hp) with
              | Or.inl lt => hrec p lt
              | Or.inr eq3 => Fin.eq_of_val_eq eq3 ▸ eq ▸ eq2.symm
            concl )
          (fun _ => True.intro)
    )
  Except.allP_mp ind (fun () h p => h p p.isLt)


def checkTerminal_err_correct {a: Nat} {r s: NatCDFA a} {m: DFSTable r s}:
    (checkTerminal r s m).allEP (fun l =>
      ∃ p: Fin r.n, ∃ q: Fin s.n, (m.get p) = some (q, l.reverse) ∧ s.f q ≠ r.f p) :=
  Fin.foldlM_induction (motive := fun (acc: Except _ _) _ => acc.allEP _)
    (Except.pure_def ▸ True.intro)
    (fun acc p hrec => match acc with
      | Except.error _ => hrec
      | Except.ok _ => match eq: Vector.get m p with
        | none => True.intro
        | some (q, _) => iteInduction (fun _ => True.intro)
          (fun ne => ⟨p, q, List.reverse_reverse _ ▸ eq, ne⟩)
    )


/-
The final, clean API
-/
public section
namespace NatCDFA

inductive MorphismObstruction {a: Nat} (r s: NatCDFA a) where
  | state: (l1: List (Fin a)) → (l2: List (Fin a)) →
    (r.advance l1 = r.advance l2) → (s.advance l1 ≠ s.advance l2) → MorphismObstruction r s
  | final: (l: List (Fin a)) → r.accepts l ≠ s.accepts l → MorphismObstruction r s


inductive FindMorphismResult {a: Nat} (r s: NatCDFA a) where
  | morphism: (f: Fin r.n → Fin s.n) → (NatCDFA.morphism r s f) → FindMorphismResult r s
  | obstruction: MorphismObstruction r s → FindMorphismResult r s


def findMorphism {a: Nat} (r s: NatCDFA a): FindMorphismResult r s :=
  match eq: dfsFindMorphism r s with
  | Except.ok acc => have h := eq ▸ dfsFindMorphism_ok_correct (r := r) (s := s)
    match eq2: checkTerminal r s acc with
    | Except.ok () => FindMorphismResult.morphism (fun i => (((acc.get i).map Prod.fst).getD s.i))
      (fun l => have ⟨_, eqm⟩ := h.right l
        ⟨
          (congrArg (fun opt => (opt.map Prod.fst).getD s.i) eqm).trans rfl,
          eqm.subst ((eq2 ▸ checkTerminal_ok_correct) (r.advance l))
        ⟩
      )
    | Except.error l => FindMorphismResult.obstruction (MorphismObstruction.final l
      (
        have ⟨p, q, eq3, ne⟩ := eq2 ▸ checkTerminal_err_correct (r := r) (s := s) (m := acc)
        have hlr: r.advance l = p :=
          (congrArg r.advance (List.reverse_reverse _).symm).trans (eq3.subst (h.left p))
        have ⟨_, eq4⟩ := h.right l
        have hls: s.advance l = q := (Prod.mk.inj (Option.some_inj.mp ((hlr ▸ eq4).symm.trans eq3))).left
        fun abs => ne (((congrArg s.f hls.symm).trans abs.symm).trans (congrArg r.f hlr))
      ))
  | Except.error (l1, l2) =>
    have h := eq ▸ dfsFindMorphism_err_correct (r := r) (s := s)
    FindMorphismResult.obstruction (MorphismObstruction.state l1 l2 h.left h.right)


theorem not_existsMorphism_of_obstruction {a: Nat} {r s: NatCDFA a} (obstruction: MorphismObstruction r s):
    ¬NatCDFA.existsMorphism r s :=
  fun ⟨f, hf⟩ => match obstruction with
  | MorphismObstruction.state l1 l2 hr hs =>
    hs (((hf l1).left.symm.trans (congrArg f hr)).trans (hf l2).left)
  | MorphismObstruction.final l hl => hl (hf l).right

end NatCDFA
end
