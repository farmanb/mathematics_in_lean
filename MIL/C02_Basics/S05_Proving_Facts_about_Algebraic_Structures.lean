import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm <;>
  · refine le_inf ?_ ?_
    · exact inf_le_right
    · exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact le_trans inf_le_left inf_le_left
    · refine le_inf ?_ ?_
      · exact le_trans inf_le_left inf_le_right
      · exact inf_le_right
  · refine le_inf ?_ ?_
    · refine le_inf ?_ ?_
      · exact inf_le_left
      · exact le_trans inf_le_right inf_le_left
    · exact le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm <;>
  · refine sup_le ?_ ?_
    · exact le_sup_right
    · exact le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · exact le_sup_left
      · exact le_trans le_sup_left le_sup_right
    · exact le_trans le_sup_right le_sup_right
  · refine sup_le ?_ ?_
    · exact le_trans le_sup_left le_sup_left
    · refine sup_le ?_ ?_
      · exact le_trans le_sup_right le_sup_left
      · exact le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left
  · refine le_inf ?_ ?_
    · exact Preorder.le_refl x
    · exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact Preorder.le_refl x
    · exact inf_le_left
  · exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

/- Nope. -/
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

/- Also nope. -/
example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← neg_add_cancel a, sub_eq_neg_add]
  exact add_le_add_left h (-a)

example (h: 0 ≤ b - a) : a ≤ b := calc
  a = a + 0 := by rw [add_zero]
  _ ≤ a + (b - a) := add_le_add_left h a
  _= b := by
    rw [add_comm, sub_add, sub_self, sub_zero]

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₀ : 0 ≤ b - a := calc
    0 = -a + a := by rw [neg_add_cancel]
    _ ≤ -a + b := add_le_add_left h (-a)
    _ = b + -a := by rw[add_comm]
    _ = b - a := by exact Mathlib.Tactic.RingNF.add_neg b a

  have h₁ : 0 ≤ (b - a) * c := by exact mul_nonneg h₀ h'
  rw [sub_mul] at h₁
  have h₂ := add_le_add_left h₁ (a*c)
  rw [add_zero, add_sub, add_comm, ← add_sub, sub_self, add_zero] at h₂
  exact h₂

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y + dist x y := calc
    0 = dist x x := by rw[dist_self]
    _ ≤ dist x y + dist y x := dist_triangle x y x
    _ = dist x y + dist x y := by rw [dist_comm y x]
  apply nonneg_add_self_iff.mp h

end
