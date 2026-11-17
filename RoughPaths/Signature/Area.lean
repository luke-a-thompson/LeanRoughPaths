import HopfAlgebras.Words.AreaGeneration
import RoughPaths.Signature.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Signatures are determined by their iterated areas

A signature is an algebra homomorphism on the shuffle algebra
(`Signature.pairing`). Since areas of areas generate the shuffle algebra,
two signatures with the same iterated areas are equal, and agreement of
the areas up to a weight gives agreement of the signatures up to that
weight.
-/

namespace RoughPaths

open HopfAlgebras HopfAlgebras.ShuffleAlgebra

namespace Signature

variable {α R : Type*} [CommRing R]

noncomputable section

/-- A signature, as an algebra homomorphism on the shuffle algebra. -/
def pairing (S : Signature α R) : ShuffleAlgebra R α →ₐ[R] R :=
  AlgHom.ofLinearMap (ShuffleAlgebra.lift fun w => S w)
    (by rw [one_def, lift_word]; exact S.coeff_nil)
    (fun p q => by
      have h : (mulₗ (R := R) (α := α)).compr₂ (ShuffleAlgebra.lift fun w => S w) =
          (LinearMap.mul R R).compl₁₂ (ShuffleAlgebra.lift fun w => S w)
            (ShuffleAlgebra.lift fun w => S w) := by
        apply linearMap_ext; intro u
        apply linearMap_ext; intro v
        simpa [← mul_def, map_list_sum, List.map_map, Function.comp_def,
          Word.shuffleCoeff, Word.coeff, coeff_apply] using (S.shuffle u v).symm
      exact LinearMap.congr_fun (LinearMap.congr_fun h p) q)

@[simp] theorem pairing_word (S : Signature α R) (w : List α) :
    pairing S (word w) = S w := lift_word _ _

/-- The signature coordinate of a letter or nested signed area. -/
def areaCoeff (S : Signature α R) (t : AreaExpr α) : R := pairing S t.eval

@[simp] theorem areaCoeff_letter (S : Signature α R) (a : α) :
    S.areaCoeff (.letter a) = S [a] := pairing_word S [a]

variable [Algebra ℚ R]

/-- Agreement on the iterated areas up to a weight determines the
signature on every word up to that weight. -/
theorem eq_of_area_eq_weight (S T : Signature α R) (weight : α → ℕ) (n : ℕ)
    (h : ∀ t : AreaExpr α, t.sum weight ≤ n → S.areaCoeff t = T.areaCoeff t)
    (w : List α) (hw : (w.map weight).sum ≤ n) : S w = T w := by
  rw [← pairing_word S w, ← pairing_word T w]
  refine LinearMap.eqOn_span (f := (pairing S).toLinearMap) (g := (pairing T).toLinearMap) ?_
    (word_mem_areaSpan weight w)
  rintro _ ⟨ts, hts, rfl⟩
  simp only [AlgHom.toLinearMap_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun t ht => ?_)
  exact h t ((List.single_le_sum (fun _ _ => Nat.zero_le _) _
    (List.mem_map.mpr ⟨t, ht, rfl⟩)).trans (hts.le.trans hw))

/-- **The iterated areas determine the whole signature.** -/
theorem ext_of_area_eq (S T : Signature α R)
    (h : ∀ t, S.areaCoeff t = T.areaCoeff t) : S = T := by
  apply Subtype.ext
  funext w
  exact eq_of_area_eq_weight S T (fun _ => 0) 0 (fun t _ => h t) w (by simp)

end
end Signature
end RoughPaths
