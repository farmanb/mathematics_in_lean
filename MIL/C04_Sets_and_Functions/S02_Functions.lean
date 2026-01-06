import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x hxs
    exact h ⟨x, hxs, rfl⟩
  · rintro h y ⟨x, hxs, hfxy⟩
    simpa [hfxy] using h hxs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro a ha
  rcases ha with ⟨b,hbs, hfbfa⟩
  rw [← h hfbfa]
  exact hbs

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, hx, hfx⟩
  simpa [hfx] using hx

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  rcases h y with ⟨x, hfx⟩
  refine ⟨x, ?_, hfx⟩
  simpa [hfx] using hy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, hxs, hfx⟩
  exact ⟨x, h hxs, hfx⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro hx
    rcases hx with (h₁ | h₂)
    left; assumption
    right; assumption
  · rintro (h₁ | h₂)
    exact mem_union_left _ h₁
    exact mem_union_right _ h₂

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨hxs, hxt⟩, hfx⟩
  constructor
  · exact ⟨x, hxs, hfx⟩
  · exact ⟨x, hxt, hfx⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨a, has, hfa⟩, ⟨b, hbt, hfb⟩⟩
  refine ⟨a, ?_, hfa⟩
  refine ⟨has, ?_⟩
  rw[h (Eq.trans hfa (Eq.symm hfb))]
  exact hbt

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨a, has, hfa⟩, h₂⟩
  refine ⟨a, ?_, hfa⟩
  refine ⟨has, ?_⟩
  intro hat
  apply h₂
  exact ⟨a, hat, hfa⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨hfxu, hnfxv⟩
  exact ⟨hfxu, hnfxv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro ⟨⟨x, hxs, hfx⟩, hyv⟩
    refine ⟨x, ?_ , hfx⟩
    refine ⟨hxs, ?_⟩
    simpa [hfx] using hyv
  · rintro ⟨x, ⟨⟨hxs, (hfxv : f x ∈ v)⟩, hfx⟩⟩
    constructor
    · exact ⟨x, hxs, hfx⟩
    · simpa [hfx] using hfxv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y ⟨x, ⟨hxs, (hfxu : f x ∈ u)⟩, hfx⟩
  constructor
  · exact ⟨x, hxs, hfx⟩
  · simpa [hfx] using hfxu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨hxs, hfxu⟩
  constructor
  · exact ⟨x, hxs, rfl⟩
  · exact hfxu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (hxs | (hfxu : f x ∈ u))
  · exact mem_union_left _ ⟨x, hxs, rfl⟩
  · exact mem_union_right _ hfxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · rintro ⟨x, hx, hfx⟩
    rcases mem_iUnion.mp hx with ⟨i, hxAi⟩
    apply mem_iUnion.mpr
    exact ⟨i, ⟨x, hxAi, hfx⟩⟩
  · intro hy
    rcases mem_iUnion.mp hy with ⟨i, ⟨x, hxAi, hfx⟩⟩
    refine ⟨x, mem_iUnion.mpr ⟨i, hxAi⟩, hfx⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y ⟨x, hx, hfx⟩
  apply mem_iInter.mpr
  intro i
  refine ⟨x, mem_iInter.mp hx i, hfx⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy
  rcases mem_iInter.mp hy i with ⟨a, haAi, hfa⟩
  refine ⟨a, ?_, hfa⟩
  apply mem_iInter.mpr
  intro j
  rcases mem_iInter.mp hy j with ⟨b, hbAj, hfb⟩
  simpa [injf (Eq.trans hfa (Eq.symm hfb))] using hbAj

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor <;>
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hfxBi⟩
    exact mem_iUnion.mpr ⟨i, hfxBi⟩

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor <;>
  · intro hx
    apply mem_iInter.mpr
    intro i
    exact mem_iInter.mp hx i


example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro _ h₁ _ h₂ hsqrt
  exact (sqrt_inj h₁ h₂).mp hsqrt

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro a ha b hb hf
  dsimp at hf
  have ha₁ : a = sqrt (a^2) := Eq.symm (sqrt_sq ha)
  have hb₁ : b = sqrt (b^2) := Eq.symm (sqrt_sq hb)
  rw [ha₁, hb₁]
  exact congrArg sqrt hf

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x,hxpos, hsqrtx⟩
    rw [Set.mem_setOf] at hxpos
    exact le_trans (ge_iff_le.mp (sqrt_nonneg x)) (le_of_eq hsqrtx)
  · intro (hy : y ≥ 0)
    exact ⟨y^2, sq_nonneg y, sqrt_sq hy⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x, (hx : x^2 = y)⟩
    exact le_trans (sq_nonneg x) (le_of_eq hx)
  · intro (hy : y ≥ 0)
    exact ⟨√y, sq_sqrt hy⟩

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro hinjf x
    exact hinjf (inverse_spec (f x) ⟨x, rfl⟩)
  · intro h a b hab
    calc a = inverse f (f a) := Eq.symm (h a)
      _ = inverse f (f b) := congrArg (inverse f) hab
      _ = b := h b

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro hsurjf y
    exact inverse_spec y (hsurjf y)
  · intro h y
    refine ⟨inverse f y, h y⟩

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    exact Eq.mpr_not (congrFun (id (Eq.symm h)) j) h₁

  contradiction

-- COMMENTS: TODO: improve this
end
