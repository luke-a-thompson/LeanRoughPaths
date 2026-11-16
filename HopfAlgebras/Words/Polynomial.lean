import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.BilinearMap

/-! # Finite rational word polynomials

Rational linear combinations of words, with linear and bilinear extension
of operations defined on words.
-/

namespace HopfAlgebras.Word

abbrev Polynomial (α : Type*) := List α →₀ ℚ

namespace Polynomial

variable {α : Type*}
noncomputable section

/-- The polynomial consisting of one word. -/
def word (w : List α) : Polynomial α := Finsupp.single w 1

/-- Extend a function on words linearly. -/
def lift {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f : List α → V) : Polynomial α →ₗ[ℚ] V := Finsupp.linearCombination ℚ f

@[simp] theorem lift_word {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f : List α → V) (w : List α) : lift f (word w) = f w := by
  simp [lift, word]

/-- Bilinear extension of an operation on words. -/
def lift₂ (f : List α → List α → Polynomial α) :
    Polynomial α →ₗ[ℚ] Polynomial α →ₗ[ℚ] Polynomial α :=
  lift (fun u => lift (f u))

@[simp] theorem lift₂_word (f : List α → List α → Polynomial α) (u v : List α) :
    lift₂ f (word u) (word v) = f u v := by simp [lift₂]

@[ext] theorem linearMap_ext {V : Type*} [AddCommGroup V] [Module ℚ V]
    {f g : Polynomial α →ₗ[ℚ] V} (h : ∀ w, f (word w) = g (word w)) : f = g := by
  apply Finsupp.lhom_ext
  intro w c
  have hc : Finsupp.single w c = c • word w := by simp [word]
  rw [hc, map_smul, map_smul, h]

end
end Polynomial
end HopfAlgebras.Word
