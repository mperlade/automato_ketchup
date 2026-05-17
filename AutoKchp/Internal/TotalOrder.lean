module


public section

variable {α: Type}

class TotalOrd α extends LE α where
  le_decidable: DecidableLE α
  eq_decidable: DecidableEq α
  le_refl: ∀ (a: α), le a a
  le_trans: ∀ {a b c: α}, le a b → le b c → le a c
  le_antisymm: ∀ {a b: α}, le a b → le b a → a = b
  le_total: ∀ (a b: α), le a b ∨ le b a


instance [t: TotalOrd α]: DecidableLE α := t.le_decidable
instance [t: TotalOrd α]: DecidableEq α := t.eq_decidable
instance [t: TotalOrd α]: LT α := ⟨fun x y => x ≤ y ∧ x ≠ y⟩
instance [t: TotalOrd α]: DecidableLT α := fun _ _ => instDecidableAnd


theorem TotalOrd.lt_trans [t: TotalOrd α] {a b c: α} (h1: a < b) (h2: b < c): a < c :=
  ⟨
    t.le_trans h1.left h2.left,
    fun eq => h1.right (t.le_antisymm h1.left (eq ▸ h2.left))
  ⟩

end
