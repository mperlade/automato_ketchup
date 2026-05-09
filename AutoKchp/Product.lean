module

public import AutoKchp.NatCDFA


theorem pack_lt {n m a b: Nat} (ha: a < n) (hb: b < m):
    a * m + b < n * m :=
  have blt: a * m + b < a * m + m := Nat.add_lt_add_left hb (a * m)
  have eq: a * m + m = (a + 1) * m :=
    Nat.add_mul a 1 m ▸ congrArg (a * m + ·) (Nat.one_mul m).symm
  have alt: (a + 1) * m ≤ n * m := Nat.mul_le_mul_right m (Nat.add_one_le_of_lt ha)
  Nat.lt_of_lt_of_le (eq ▸ blt) alt


def pack {n m: Nat} (x: Fin n × Fin m): Fin (n * m) :=
  ⟨x.fst.val * m + x.snd.val, pack_lt x.fst.isLt x.snd.isLt⟩


def unpack {n m: Nat} (y: Fin (n * m)): Fin n × Fin m :=
  (
    ⟨y.val / m, Nat.div_lt_of_lt_mul (Nat.mul_comm n m ▸ y.isLt)⟩,
    ⟨y.val % m, Nat.mod_lt y.val (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt y.isLt))⟩,
  )


theorem pack_unpack {n m: Nat} {y: Fin (n * m)}:
    pack (unpack y) = y :=
  Fin.eq_of_val_eq (Nat.div_add_mod' y.val m)


theorem unpack_pack {n m: Nat} {x: Fin n × Fin m}:
    unpack (pack x) = x :=
  Prod.ext
    (Fin.eq_of_val_eq (Nat.div_eq_of_lt_le
      (Nat.le_add_right _ x.snd.val)
      (Nat.add_one_mul x.fst.val m ▸ Nat.add_lt_add_left x.snd.isLt (x.fst.val * m))
    ))
    (Fin.eq_of_val_eq (
      (Nat.mul_add_mod_self_right x.fst.val m x.snd.val).trans
        (Nat.mod_eq_of_lt x.snd.isLt)
    ))


def constructProduct {a: Nat} (r s: NatCDFA a) (p: Bool → Bool → Bool): NatCDFA a := {
  n := r.n * s.n
  δ := fun i b => (fun (ri, si) => pack (r.δ ri b, s.δ si b)) (unpack i)
  i := pack (r.i, s.i)
  f := fun i => (fun (ri, si) => p (r.f ri) (s.f si)) (unpack i)
}


theorem product_δ {a: Nat} {r s: NatCDFA a} {p: Bool → Bool → Bool}
  {i: Fin r.n} {j: Fin s.n} {b: Fin a}:
    (constructProduct r s p).δ (pack (i, j)) b = pack (r.δ i b, s.δ j b) :=
  have concl: pack (r.δ (unpack (pack (i, j))).fst b, s.δ (unpack (pack (i, j))).snd b)
    = pack (r.δ i b, s.δ j b) := unpack_pack ▸ rfl
  concl


theorem product_advanceFrom {a: Nat} {r s: NatCDFA a} {p: Bool → Bool → Bool}
  {i: Fin r.n} {j: Fin s.n}:
    {l: List (Fin a)} → (constructProduct r s p).advanceFrom (pack (i, j)) l =
      pack (r.advanceFrom i l, s.advanceFrom j l)
  | [] => rfl
  | h::t =>
    have concl: (constructProduct r s p).advanceFrom ((constructProduct r s p).δ (pack (i, j)) h) t =
        pack (r.advanceFrom (r.δ i h) t, s.advanceFrom (s.δ j h) t) :=
      product_δ ▸ product_advanceFrom
    concl


theorem product_f {a: Nat} {r s: NatCDFA a} {p: Bool → Bool → Bool}
  {i: Fin r.n} {j: Fin s.n}:
    (constructProduct r s p).f (pack (i, j)) = p (r.f i) (s.f j) :=
  have concl: p (r.f (unpack (pack (i, j))).fst) (s.f (unpack (pack (i, j))).snd) = p (r.f i) (s.f j) :=
    unpack_pack ▸ rfl
  concl


theorem product_accepts {a: Nat} {r s: NatCDFA a} {p: Bool → Bool → Bool} {l: List (Fin a)}:
    (constructProduct r s p).accepts l = p (r.accepts l) (s.accepts l) :=
  Eq.trans (product_advanceFrom ▸ rfl) product_f


public section
namespace NatCDFA

structure ProductResult {a: Nat} (r s: NatCDFA a) (p: Bool → Bool → Bool) where
  product: NatCDFA a
  correct: ∀ l: List (Fin a), product.accepts l = p (r.accepts l) (s.accepts l)


def product {a: Nat} (r s: NatCDFA a) (p: Bool → Bool → Bool): ProductResult r s p := {
  product := constructProduct r s p
  correct := fun _ => product_accepts
}

end NatCDFA
end
