import HopfAlgebras.Words.AreaGeneration
import RoughPaths.Signature.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Signature coordinates determined by iterated areas -/

namespace RoughPaths

open HopfAlgebras
open HopfAlgebras.Word.Polynomial

namespace Signature

variable {α R : Type*} [CommRing R] [Algebra ℚ R]
noncomputable section

/-- Pair a signature with a finite rational word polynomial. -/
def pairing (S : Signature α R) : HopfAlgebras.Word.Polynomial α →ₗ[ℚ] R :=
  lift (fun w => S w)

@[simp] theorem pairing_word (S : Signature α R) (w : List α) :
    pairing S (word w) = S w := lift_word _ _

/-- The signature coordinate of a letter or nested signed area. -/
def areaCoeff (S : Signature α R) (t : Word.AreaExpr α) : R := pairing S (evalArea t)

@[simp] theorem areaCoeff_letter (S : Signature α R) (a : α) :
    S.areaCoeff (.letter a) = S [a] := pairing_word S [a]

theorem pairing_shuffle (S : Signature α R) (p q : HopfAlgebras.Word.Polynomial α) :
    pairing S (HopfAlgebras.Word.Polynomial.shuffle p q) = pairing S p * pairing S q := by
  have h : HopfAlgebras.Word.Polynomial.shuffle.compr₂ (pairing S) =
      (LinearMap.mul ℚ R).compl₁₂ (pairing S) (pairing S) := by
    apply linearMap_ext; intro u
    apply linearMap_ext; intro v
    simpa [map_list_sum, List.map_map, Function.comp_def,
      Word.shuffleCoeff, Word.coeff, coeff_apply] using (S.shuffle u v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

@[simp] theorem pairing_prod (S : Signature α R) (ps : List (HopfAlgebras.Word.Polynomial α)) :
    pairing S (prod ps) = (ps.map (pairing S)).prod := by
  induction ps with
  | nil => simpa only [prod, pairing_word, List.map_nil, List.prod_nil, coeff_apply] using S.coeff_nil
  | cons p ps ih => simp [prod, pairing_shuffle, ih]

/-- Agreement on area expressions contained in a word's letter multiset
suffices to determine that word. -/
theorem eq_of_area_eq (S T : Signature α R) (w : List α)
    (h : ∀ t : HopfAlgebras.Word.AreaExpr α, t.content ≤ (↑w : Multiset α) →
      S.areaCoeff t = T.areaCoeff t) : S w = T w := by
  rw [← pairing_word S w, ← pairing_word T w]
  apply LinearMap.eqOn_span ?_ (word_generated w)
  rintro _ ⟨ts, hts, rfl⟩
  simp only [pairing_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro t ht
  exact h t (hts ▸ List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩))

/-- A weighted truncation needs only areas up to that same weight.
Weights may be zero; positivity is not needed for this finite-word result. -/
theorem eq_of_area_eq_weight (S T : Signature α R) (weight : α → ℕ) (n : ℕ)
    (h : ∀ t : HopfAlgebras.Word.AreaExpr α, (t.content.map weight).sum ≤ n →
      S.areaCoeff t = T.areaCoeff t)
    (w : List α) (hw : (w.map weight).sum ≤ n) : S w = T w := by
  apply eq_of_area_eq
  intro t ht
  apply h
  obtain ⟨s, hs⟩ := exists_add_of_le ht
  have he := congrArg (fun m : Multiset α => (m.map weight).sum) hs
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_coe, Multiset.sum_coe] at he
  omega

/-- The iterated areas determine the whole signature. -/
theorem ext_of_area_eq (S T : Signature α R)
    (h : ∀ t, S.areaCoeff t = T.areaCoeff t) : S = T := by
  apply Subtype.ext
  funext w
  exact eq_of_area_eq S T w (fun t _ => h t)

end
end Signature
end RoughPaths
