import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (hxst | hxsu)
  · exact ⟨hxst.1, mem_union_left u hxst.2⟩
  · exact ⟨hxsu.1, mem_union_right t hxsu.2⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨hxs, hnxtu⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hxs,?_⟩
    intro hxt
    exact hnxtu (mem_union_left u hxt)
  · intro hxu
    exact hnxtu (mem_union_right t hxu)

example : s ∩ t = t ∩ s := by
  ext _
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _ ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm <;>
  · intro x hx
    exact ⟨hx.2, hx.1⟩

example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    refine ⟨hx, mem_union_left t hx⟩

example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  · intro x hx
    rcases hx with (h₁ | h₂)
    · assumption
    · exact h₂.1
  · intro x hx
    exact mem_union_left (s ∩ t) hx

example : s \ t ∪ t = s ∪ t := by
  apply Subset.antisymm
  · rintro x (⟨hxs, hnxt⟩ | hxt)
    · exact mem_union_left t hxs
    · exact mem_union_right s hxt
  · rintro x (hxs | hxt)
    · rcases em (x ∈ t) with (hxt | hnxt)
      · exact mem_union_right _ hxt
      · exact mem_union_left _ ⟨hxs, hnxt⟩
    · exact mem_union_right _ hxt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  · rintro x (⟨hxs, hnxt⟩ | ⟨hxt, hnxs⟩)
    · refine ⟨mem_union_left _ hxs, ?_⟩
      · intro hxst
        exact hnxt (hxst.2)
    · refine ⟨mem_union_right _ hxt, ?_⟩
      intro hxst
      exact hnxs hxst.1
  · rintro x ⟨hxst, hnxst⟩
    rcases em (x ∈ s) with (hxs | hnxs)
    · refine mem_union_left _ ⟨hxs, ?_⟩
      intro hxt
      exact hnxst ⟨hxs, hxt⟩
    · refine mem_union_right _ ⟨?_, hnxs⟩
      by_contra hnxt
      rcases hxst with (hxs | hxt)
      · exact hnxs hxs
      · exact hnxt hxt

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  rintro ⟨hnprime, hn2⟩
  rw [Set.mem_setOf] at *
  rintro ⟨k,hk⟩
  rw [← two_mul] at hk
  unfold Nat.Prime at hnprime
  rcases (hnprime.isUnit_or_isUnit hk) with (h₁ | h₂)
  · exact Nat.prime_two.not_isUnit h₁
  · have : k = 1 := Nat.isUnit_iff.mp h₂
    rw [Nat.isUnit_iff.mp h₂, mul_one] at hk
    exact Ne.symm (Nat.ne_of_lt hn2) hk

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x hxs
  exact⟨h₀ x (ssubt hxs), h₁ x (ssubt hxs)⟩

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, hxs, hnxeven, hxprime⟩
  exact ⟨x, ssubt hxs, hxprime⟩

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  rw [mem_union, mem_iInter, mem_iInter]
  constructor
  · rintro (hxs | hxAi) <;> intro i
    · exact mem_union_right _ hxs
    · exact mem_union_left _ (hxAi i)
  · intro h
    rcases em (x ∈ s) with (hxs | hnxs)
    · exact Or.intro_left _ hxs
    · refine Or.intro_right _ ?_
      intro i
      rcases (h i) with (_ | hxs)
      · assumption
      · by_contra;
        exact hnxs hxs

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd


lemma aux (n : ℕ) : ∃ p ∈ primes, n ≤ p := by sorry

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  ext x
  constructor
  · intro h
    trivial
  · intro hx
    simp only [mem_iUnion, mem_setOf_eq, exists_prop, aux x]
end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
