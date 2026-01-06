import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, lbfa⟩
  rcases (h a) with ⟨x, hx⟩
  have : a < a := calc
    a ≤ f x := lbfa x
    _ < a := hx
  exact (lt_self_iff_false a).mp this

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, uba⟩
  linarith [uba (a + 1)]

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra hnlt
  rcases eq_or_lt_of_not_gt hnlt with (heq | hlt)
  · linarith [congrArg f heq]
  · linarith [h (le_of_lt hlt)]

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hfmono
  linarith [hfmono h]

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b hab
    rw [show f a = 0 by rfl]
  have h' : f 1 ≤ f 0 := le_refl _
  linarith [h (f := f) monof (a := 1) (b := 0) h']

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro hx
  rcases exists_between hx with ⟨a, hapos, hax⟩
  linarith [h a hapos]

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x hx
  apply h
  exact ⟨x, hx⟩

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, hx⟩
  exact h x hx

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra! h'
  apply h
  intro x
  exact h' x

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  push_neg
  by_contra! h'
  rcases h with ⟨x, hx⟩
  exact hx (h' x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  intro h'
  exact h' h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra! h'
  apply h
  refine ⟨a, ?_⟩
  intro x
  exact h' x

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  by_contra! h'
  apply h
  intro a b hab
  exact h' a b hab

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
