import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  calc |s n + t n - (a + b)|
  _ = |(s n - a) + (t n - b)| := by ring_nf
  _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
  _ < ε/2 + ε/2 := by
    refine add_lt_add ?_ ?_
    · exact hs n (ge_trans hn (Nat.le_max_left Ns Nt))
    · exact ht n (ge_trans hn (Nat.le_max_right Ns Nt))
  _ = ε := add_halves ε

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  unfold ConvergesTo
  intro ε εpos
  have εcpos : ε/|c| > 0 := div_pos εpos acpos
  rcases cs (ε/|c|) εcpos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  dsimp
  calc |c * s n - c * a| = |c*(s n - a)| := by ring_nf
    _ = |c| * |s n - a| := abs_mul c (s n - a)
    _ < |c| * (ε / |c|) := (mul_lt_mul_left acpos).mpr (hN n hn)
    _ = (|c| / |c|) * ε := by ring_nf
    _ = ε := by rw [div_self (abs_ne_zero.mpr h), one_mul]

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc |s n| = |s n - a + a| := by ring_nf
  _ ≤ |s n - a| + |a| := abs_add_le (s n - a) a
  _ < 1 + |a| := (add_lt_add_iff_right |a|).mpr (h n hn)
  _ = |a| + 1 := by rw [add_comm]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  refine ⟨max N₀ N₁, ?_⟩
  intro n hn
  calc |s n * t n - 0|
    _ = |s n * (t n - 0)| := by ring_nf
    _ = |s n| * |t n - 0| := abs_mul (s n) (t n - 0)
    _ ≤ |s n| * (ε/B) := by
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
      · exact Preorder.le_refl |s n|
      · apply le_of_lt (h₁ n (le_of_max_le_right hn))
      · exact abs_nonneg (s n)
      · apply le_of_lt pos₀
    _ < B * (ε / B) := by
      refine mul_lt_mul_of_pos_of_nonneg' ?_ ?_ pos₀ ?_
      · exact h₀ n (le_of_max_le_left hn)
      · exact Preorder.le_refl (ε / B)
      · exact le_of_lt Bpos
    _ = (B / B) * ε := by ring_nf
    _ = 1 * ε := by
      rw [div_self (by exact Ne.symm (ne_of_lt Bpos))]
    _ = ε := one_mul ε


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    exact hNa N (Nat.le_max_left Na Nb)
  have absb : |s N - b| < ε := by
    apply hNb N (Nat.le_max_right Na Nb)
  have : |a - b| < |a - b| := calc
    |a - b| = |(a - s N) + (s N - b)| := by ring_nf
    _ ≤ |a - s N| + |s N - b| := abs_add_le (a - s N) (s N - b)
    _ = |s N - a| + |s N - b| := by rw [abs_sub_comm a (s N)]
    _ < ε + ε := by exact add_lt_add absa absb
    _ = |a - b| := by
      unfold ε
      rw [add_halves]
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
