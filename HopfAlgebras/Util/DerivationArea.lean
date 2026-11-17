import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel
import HopfAlgebras.Util.List

/-!
# The signed-area form of a derivation

For a derivation `D` on a commutative ring, `D.area x y = x • D y - y • D x`
is the signed-area (Wronskian) form. The Leibniz rule rearranges to

`(m + 1) • (∏ xᵢ) • D y = D (y * ∏ xᵢ) + ∑ᵢ (∏_{j ≠ i} xⱼ) • D.area xᵢ y`,

which lowers the number of factors in front of a differential at the price
of signed areas. Every reduction of iterated integrals to areas in this
library is this identity for a particular derivation.
-/

namespace Derivation

open List (selections selections_perm)

private theorem sum_map_sub_const {M β : Type*} [AddCommGroup M] (l : List β) (c : M)
    (f : β → M) : (l.map fun p => c - f p).sum = l.length • c - (l.map f).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons, succ_nsmul]; abel

variable {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M)

/-- The signed-area form `x dy - y dx` of a derivation. -/
def area (x y : A) : M := x • D y - y • D x

@[simp] theorem area_self (x : A) : D.area x x = 0 := sub_self _

theorem area_swap (x y : A) : D.area x y = -D.area y x := (neg_sub _ _).symm

/-- The Leibniz rule for a product of a list. -/
theorem leibniz_list_prod (xs : List A) :
    D xs.prod = ((selections xs).map fun p => p.2.prod • D p.1).sum := by
  induction xs with
  | nil => simp [selections]
  | cons x xs ih =>
      simp only [List.prod_cons, D.leibniz, ih, selections, List.map_cons, List.sum_cons,
        List.map_map, Function.comp_def, List.smul_sum, mul_smul]
      abel

/-- **Area reduction.** Integration by parts, with the boundary term
`D (y * ∏ xᵢ)` and one signed area for each factor. -/
theorem length_succ_nsmul_prod_smul (xs : List A) (y : A) :
    (xs.length + 1) • (xs.prod • D y) =
      D (y * xs.prod) + ((selections xs).map fun p => p.2.prod • D.area p.1 y).sum := by
  have hterm : ∀ p ∈ selections xs,
      p.2.prod • D.area p.1 y = xs.prod • D y - y • (p.2.prod • D p.1) := by
    intro p hp
    have hprod : p.1 * p.2.prod = xs.prod := by simpa using (selections_perm hp).prod_eq
    simp only [area, smul_sub, smul_smul]
    rw [mul_comm p.2.prod p.1, hprod, mul_comm p.2.prod y]
  rw [List.map_congr_left hterm, sum_map_sub_const, List.selections_length, D.leibniz,
    D.leibniz_list_prod, List.smul_sum, List.map_map, succ_nsmul]
  simp only [Function.comp_def]
  abel

end Derivation
