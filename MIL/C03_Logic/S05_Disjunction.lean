import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  exact le_max_left x (-x)

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  exact le_max_right x (-x)

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  apply max_le
  · exact add_le_add (le_abs_self x) (le_abs_self y)
  · rw [neg_add]
    exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    exact lt_max_iff.mp h
  · rintro (h₁ | h₂)
    · exact lt_of_lt_of_le h₁ (le_abs_self y)
    · exact lt_of_lt_of_le h₂ (neg_le_abs_self y)

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    constructor
    · exact neg_lt.mpr (lt_of_le_of_lt (neg_le_abs_self x) h)
    · exact lt_of_le_of_lt (le_abs_self x) h
  · rintro ⟨h₁, h₂⟩
    exact max_lt (a := x) (b := -x) (c := y) h₂ (neg_lt.mp h₁)

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h⟩
  have h' : x^2 + y^2 ≥ 0 := calc
    x^2 + y^2 ≥ 0 + 0 := add_le_add (sq_nonneg x) (sq_nonneg y)
    _ = 0 := add_zero 0
  rcases h with (h₁ | h₂)
  · exact le_of_le_of_eq h' (id (Eq.symm h₁))
  · calc z = x^2 + y^2 + 1 := h₂
    _ ≥ 0 + 1 := add_le_add_right h' 1
    _ = 1 := zero_add 1
    _ ≥ 0 := zero_le_one' ℝ

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  exact sq_eq_one_iff.mp h

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  exact sq_eq_one_iff.mp h

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro hpq
    cases em P
    · right
      apply hpq
      assumption
    · left; assumption
  · rintro (h₁ | h₂)
    · intro; contradiction
    · intro; assumption
