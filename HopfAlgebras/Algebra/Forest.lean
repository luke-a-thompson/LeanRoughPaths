/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Forests.Rooted
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The Algebra of Rooted Forests

This file defines the commutative algebra freely spanned by non-planar rooted
forests. This is the algebraic carrier used by rooted-tree Hopf algebras.

## Main definitions

* `ForestAlgebra` - the monoid algebra of rooted forests
* `ForestAlgebra.ofForest` - the monomial associated to a rooted forest
* `ForestAlgebra.Character` - algebra characters on the forest algebra
* `ForestAlgebra.Character.evalForest` - evaluation of one forest monomial

## References

* Philippe Chartier, Ernst Hairer, Gilles Vilmart,
  *Algebraic Structures of B-series*
* Alain Connes, Dirk Kreimer, *Hopf Algebras, Renormalization and
  Noncommutative Geometry*
-/

namespace HopfAlgebras

universe u

/-- The algebra freely spanned by rooted forests over a coefficient semiring. -/
abbrev ForestAlgebra (R : Type u) [Semiring R] : Type u :=
  AddMonoidAlgebra R RootedForest

namespace ForestAlgebra

noncomputable section

variable {R : Type u}

/-- The monomial associated to a rooted forest. -/
def ofForest [Semiring R] (φ : RootedForest) : ForestAlgebra R :=
  AddMonoidAlgebra.single φ 1

@[simp]
theorem ofForest_zero [Semiring R] : ofForest (R := R) 0 = 1 := by
  simp [ofForest, AddMonoidAlgebra.one_def]

@[simp]
theorem ofForest_empty [Semiring R] : ofForest (R := R) RootedForest.empty = 1 := by
  simp [RootedForest.empty]

@[simp]
theorem ofForest_add [Semiring R] (φ ψ : RootedForest) :
    ofForest (R := R) (φ + ψ) = ofForest φ * ofForest ψ := by
  simp [ofForest, AddMonoidAlgebra.single_mul_single]

/-- The counit value on a forest monomial. -/
def counitCoeff [Zero R] [One R] (φ : RootedForest) : R :=
  by
    classical
    exact if φ = 0 then 1 else 0

@[simp]
theorem counitCoeff_zero [Zero R] [One R] : counitCoeff (R := R) 0 = 1 := by
  classical
  simp [counitCoeff]

@[simp]
theorem counitCoeff_empty [Zero R] [One R] :
    counitCoeff (R := R) RootedForest.empty = 1 := by
  classical
  simp [RootedForest.empty]

theorem counitCoeff_ne_zero [Zero R] [One R] {φ : RootedForest} (hφ : φ ≠ 0) :
    counitCoeff (R := R) φ = 0 := by
  classical
  simp [counitCoeff, hφ]

theorem counitCoeff_add [Semiring R] (φ ψ : RootedForest) :
    counitCoeff (R := R) (φ + ψ) = counitCoeff φ * counitCoeff ψ := by
  classical
  by_cases hφ : φ = 0
  · subst φ
    simp [counitCoeff]
  · by_cases hψ : ψ = 0
    · subst ψ
      simp [counitCoeff, hφ]
    · have hφpos := (RootedForest.order_pos_iff_ne_zero φ).2 hφ
      have hψpos := (RootedForest.order_pos_iff_ne_zero ψ).2 hψ
      have hsumpos : 0 < RootedForest.order (φ + ψ) := by
        rw [RootedForest.order_add]
        omega
      have hsum : φ + ψ ≠ 0 :=
        (RootedForest.order_pos_iff_ne_zero (φ + ψ)).1 hsumpos
      simp [counitCoeff, hφ, hψ, hsum]

private def counitMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative RootedForest →* R where
  toFun φ := counitCoeff (R := R) (Multiplicative.toAdd φ)
  map_one' := by
    simp [counitCoeff]
  map_mul' φ ψ := by
    exact counitCoeff_add (R := R) (Multiplicative.toAdd φ) (Multiplicative.toAdd ψ)

/-- The counit algebra homomorphism, sending the empty forest to `1` and other forests to `0`. -/
def counit (R : Type u) [CommSemiring R] : ForestAlgebra R →ₐ[R] R :=
  (AddMonoidAlgebra.lift R R RootedForest) (counitMonoidHom R)

@[simp]
theorem counit_ofForest [CommSemiring R] (φ : RootedForest) :
    counit R (ofForest φ) = counitCoeff (R := R) φ := by
  simp [counit, ofForest, counitMonoidHom, counitCoeff]

@[simp]
theorem counit_ofForest_zero [CommSemiring R] :
    counit R (ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem counit_ofForest_ne_zero [CommSemiring R] {φ : RootedForest} (hφ : φ ≠ 0) :
    counit R (ofForest (R := R) φ) = 0 := by
  rw [counit_ofForest]
  exact counitCoeff_ne_zero hφ

/-- Algebra characters on the rooted-forest algebra. -/
abbrev Character (R : Type u) [CommSemiring R] : Type u :=
  ForestAlgebra R →ₐ[R] R

namespace Character

variable [CommSemiring R]

/-- Evaluate a character on the forest monomial associated to a rooted forest. -/
def evalForest (χ : Character R) (φ : RootedForest) : R :=
  χ (ofForest (R := R) φ)

@[simp]
theorem evalForest_zero (χ : Character R) : χ.evalForest 0 = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_empty (χ : Character R) :
    χ.evalForest RootedForest.empty = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_add (χ : Character R) (φ ψ : RootedForest) :
    χ.evalForest (φ + ψ) = χ.evalForest φ * χ.evalForest ψ := by
  simp [evalForest, ofForest_add]

theorem evalForest_ofPTree_list_perm (χ : Character R) {ts us : List PTree}
    (h : ts.Perm us) :
    χ.evalForest (ts.map RootedTree.ofPTree : RootedForest) =
      χ.evalForest (us.map RootedTree.ofPTree : RootedForest) :=
  congrArg χ.evalForest (Quotient.sound (h.map RootedTree.ofPTree))

theorem evalForest_ofPTree_list_forestPerm (χ : Character R)
    {ts us : List PTree} (h : PTree.ForestPerm ts us) :
    χ.evalForest (ts.map RootedTree.ofPTree : RootedForest) =
      χ.evalForest (us.map RootedTree.ofPTree : RootedForest) :=
  congrArg χ.evalForest h

theorem evalForest_ofPTree_list_forall₂_perm (χ : Character R)
    {ts us : List PTree} (h : List.Forall₂ PTree.Perm ts us) :
    χ.evalForest (ts.map RootedTree.ofPTree : RootedForest) =
      χ.evalForest (us.map RootedTree.ofPTree : RootedForest) :=
  congrArg χ.evalForest <|
    congrArg (fun vs : List RootedTree => (vs : RootedForest))
      (RootedTree.map_ofPTree_eq_of_forall₂_perm h)

@[ext]
theorem ext {χ ψ : Character R} (h : ∀ φ, χ.evalForest φ = ψ.evalForest φ) :
    χ = ψ := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    χ (ofForest (R := R) (Multiplicative.toAdd φ)) =
      ψ (ofForest (R := R) (Multiplicative.toAdd φ))
  exact h (Multiplicative.toAdd φ)

theorem ext_tree {χ ψ : Character R}
    (h : ∀ τ : RootedTree,
      χ.evalForest (RootedForest.singleton τ) = ψ.evalForest (RootedForest.singleton τ)) :
    χ = ψ := by
  apply ext
  intro φ
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [evalForest]
  | cons τ ts ih =>
      change
        χ.evalForest (RootedForest.singleton τ + (ts : RootedForest)) =
          ψ.evalForest (RootedForest.singleton τ + (ts : RootedForest))
      rw [evalForest_add, evalForest_add, h τ]
      exact congrArg (fun x => ψ.evalForest (RootedForest.singleton τ) * x)
        (by simpa using ih)

@[simp]
theorem map_ofForest_zero (χ : Character R) :
    χ (ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem map_ofForest_empty (χ : Character R) :
    χ (ofForest (R := R) RootedForest.empty) = 1 := by
  simp

theorem map_ofForest_add (χ : Character R) (φ ψ : RootedForest) :
    χ (ofForest (R := R) (φ + ψ)) = χ (ofForest φ) * χ (ofForest ψ) := by
  rw [ofForest_add, map_mul]

end Character

end

end ForestAlgebra

end HopfAlgebras
