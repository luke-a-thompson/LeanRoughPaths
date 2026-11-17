import HopfAlgebras.Words.Polynomial
import HopfAlgebras.Util.DerivationArea
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat

/-! # Families closed under signed area are closed under integration

Let `X : α → A` be a family in a commutative `ℚ`-algebra with a derivation
`D`, and suppose every signed area of two members is a difference of two
members: `D.area (X u) (X v) = D (X (graft u v)) - D (X (graft v u))`.
Then every `(∏ X tᵢ) • D (X v)` is `D` of an explicit polynomial in the
family, `primitive graft ts v`. This is `Derivation.length_succ_nsmul_prod_smul`
applied once per factor.

The labels are arbitrary; no tree structure or numerical method is assumed.
-/

namespace HopfAlgebras.Word.AreaReduction

open HopfAlgebras.Word.Polynomial

/-- Moment polynomials: rational combinations of monomials, evaluated in
a commutative algebra. -/
abbrev Poly := HopfAlgebras.Word.Polynomial

noncomputable section

namespace Poly

abbrev monomial {α : Type*} := word (α := α)

def eval {α R : Type*} [CommRing R] [Algebra ℚ R] (X : α → R) : Poly α →ₗ[ℚ] R :=
  lift (fun ts => (ts.map X).prod)

@[simp] theorem eval_monomial {α R : Type*} [CommRing R] [Algebra ℚ R]
    (X : α → R) (ts : List α) : eval X (monomial ts) = (ts.map X).prod := lift_word _ _

end Poly

variable {α : Type*}

open List (selections selections_map selections_rest_length)

/-- The primitive of a moment monomial against one member of the family. -/
def primitive (graft : α → α → α) (ts : List α) (v : α) : Poly α :=
  ((ts.length + 1 : ℚ)⁻¹) • (Poly.monomial (v :: ts) +
    ((selections ts).attach.map fun p =>
      primitive graft p.1.2 (graft p.1.1 v) - primitive graft p.1.2 (graft v p.1.1)).sum)
  termination_by ts.length
  decreasing_by all_goals have := selections_rest_length p.2; omega

theorem primitive_eq (graft : α → α → α) (ts : List α) (v : α) :
    primitive graft ts v = ((ts.length + 1 : ℚ)⁻¹) • (Poly.monomial (v :: ts) +
      ((selections ts).map fun p =>
        primitive graft p.2 (graft p.1 v) - primitive graft p.2 (graft v p.1)).sum) := by
  rw [primitive, List.attach_map_val (l := selections ts) (f := fun p =>
    primitive graft p.2 (graft p.1 v) - primitive graft p.2 (graft v p.1))]

/-- **Area-closed families are closed under integration.** -/
theorem derivation_primitive {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [Algebra ℚ A] [AddCommGroup M] [Module A M] [Module R M] [Module ℚ M]
    (D : Derivation R A M) (graft : α → α → α) (X : α → A)
    (harea : ∀ u v, D (X (graft u v)) - D (X (graft v u)) = D.area (X u) (X v))
    (ts : List α) (v : α) :
    D (Poly.eval X (primitive graft ts v)) = (ts.map X).prod • D (X v) := by
  induction hn : ts.length using Nat.strong_induction_on generalizing ts v with
  | _ n ih =>
    have hterms : ∀ p ∈ selections ts,
        D (Poly.eval X (primitive graft p.2 (graft p.1 v) - primitive graft p.2 (graft v p.1))) =
          (p.2.map X).prod • D.area (X p.1) (X v) := by
      intro p hp
      have hlen := selections_rest_length hp
      rw [map_sub, map_sub, ih p.2.length (by omega) p.2 _ rfl,
        ih p.2.length (by omega) p.2 _ rfl, ← smul_sub, harea]
    have hred := D.length_succ_nsmul_prod_smul (ts.map X) (X v)
    rw [selections_map, List.map_map, List.length_map] at hred
    have hsum : (selections ts).map ((⇑D ∘ ⇑(Poly.eval X)) ∘ fun p =>
        primitive graft p.2 (graft p.1 v) - primitive graft p.2 (graft v p.1)) =
        (selections ts).map fun p => (p.2.map X).prod • D.area (X p.1) (X v) :=
      List.map_congr_left hterms
    rw [primitive_eq, map_smul, map_rat_smul D, map_add, map_add, map_list_sum, map_list_sum,
      List.map_map, List.map_map, hsum, Poly.eval_monomial, List.map_cons, List.prod_cons]
    simp only [Function.comp_def] at hred
    rw [← hred, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_add, Nat.cast_one,
      inv_smul_smul₀ (by positivity)]

end
end HopfAlgebras.Word.AreaReduction
