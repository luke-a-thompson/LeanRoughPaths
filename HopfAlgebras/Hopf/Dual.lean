/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.LabelledAntipode

/-!
# Dual Convolution

This file defines convolution of linear functionals on the rooted-forest Hopf
algebras. It also records the general left inverse identity induced by the
recursive antipode after evaluating by a character.
-/

namespace HopfAlgebras

universe u v w

namespace ForestAlgebra

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- Linear functionals on the rooted-forest algebra. -/
abbrev LinearFunctional (R : Type u) [CommSemiring R] : Type u :=
  ForestAlgebra R →ₗ[R] R

end

end ForestAlgebra

namespace ForestTensorAlgebra

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- Evaluate a tensor-coded forest pair by two linear functionals. -/
def evalByLinearMaps
    (f g : ForestAlgebra.LinearFunctional R) :
    ForestTensorAlgebra R →ₗ[R] R :=
  (Finsupp.linearCombination R fun term : RootedForest × RootedForest =>
    f (ForestAlgebra.ofForest (R := R) term.1) *
      g (ForestAlgebra.ofForest (R := R) term.2)).comp
        (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem evalByLinearMaps_ofPair
    (f g : ForestAlgebra.LinearFunctional R)
    (term : RootedForest × RootedForest) :
    evalByLinearMaps f g (ofPair (R := R) term) =
      f (ForestAlgebra.ofForest (R := R) term.1) *
        g (ForestAlgebra.ofForest (R := R) term.2) := by
  rw [evalByLinearMaps, ofPair]
  change (Finsupp.linearCombination R fun term : RootedForest × RootedForest =>
      f (ForestAlgebra.ofForest (R := R) term.1) *
        g (ForestAlgebra.ofForest (R := R) term.2))
      (Finsupp.single term (1 : R)) =
    f (ForestAlgebra.ofForest (R := R) term.1) *
      g (ForestAlgebra.ofForest (R := R) term.2)
  rw [Finsupp.linearCombination_single]
  simp

theorem evalByLinearMaps_sumTerms
    (f g : ForestAlgebra.LinearFunctional R)
    (terms : List (RootedForest × RootedForest)) :
    evalByLinearMaps f g (sumTerms (R := R) terms) =
      (terms.map fun term =>
        f (ForestAlgebra.ofForest (R := R) term.1) *
          g (ForestAlgebra.ofForest (R := R) term.2)).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, evalByLinearMaps_ofPair, ih]
      rfl

theorem evalByLinearMaps_compAntipode_ofCharacter
    {R : Type u} [CommRing R] (χ : ForestAlgebra.Character R) :
    evalByLinearMaps
        ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
          (ForestAlgebra.antipode (R := R)))
        (χ : ForestAlgebra R →ₐ[R] R).toLinearMap =
      (χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
        (antipodeLeft (R := R)) := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      evalByLinearMaps
          ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
            (ForestAlgebra.antipode (R := R)))
          (χ : ForestAlgebra R →ₐ[R] R).toLinearMap x =
        ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
          (antipodeLeft (R := R))) x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps
          ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
            (ForestAlgebra.antipode (R := R)))
          (χ : ForestAlgebra R →ₐ[R] R).toLinearMap
          (ofPair (R := R) term) =
        χ (antipodeLeft (R := R) (ofPair (R := R) term))
    rw [evalByLinearMaps_ofPair, antipodeLeft_ofPair]
    simp [LinearMap.comp_apply]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

theorem evalByLinearMaps_compRightAntipode_ofCharacter
    {R : Type u} [CommRing R] (χ : ForestAlgebra.Character R) :
    evalByLinearMaps
        (χ : ForestAlgebra R →ₐ[R] R).toLinearMap
        ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
          (ForestAlgebra.rightAntipode (R := R))) =
      (χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
        (antipodeRight (R := R)) := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      evalByLinearMaps
          (χ : ForestAlgebra R →ₐ[R] R).toLinearMap
          ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
            (ForestAlgebra.rightAntipode (R := R))) x =
        ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
          (antipodeRight (R := R))) x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps
          (χ : ForestAlgebra R →ₐ[R] R).toLinearMap
          ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
            (ForestAlgebra.rightAntipode (R := R)))
          (ofPair (R := R) term) =
        χ (antipodeRight (R := R) (ofPair (R := R) term))
    rw [evalByLinearMaps_ofPair, antipodeRight_ofPair]
    simp [LinearMap.comp_apply]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

end

end ForestTensorAlgebra

namespace ForestAlgebra

namespace LinearFunctional

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- The counit as a linear functional. -/
def counit (R : Type u) [CommSemiring R] : ForestAlgebra.LinearFunctional R :=
  (ForestAlgebra.counit R).toLinearMap

/-- The linear functional underlying a forest-algebra character. -/
def ofCharacter (χ : ForestAlgebra.Character R) :
    ForestAlgebra.LinearFunctional R :=
  (χ : ForestAlgebra R →ₐ[R] R).toLinearMap

/-- Evaluate a linear functional on the forest monomial associated to a rooted forest. -/
def evalForest (f : ForestAlgebra.LinearFunctional R) (φ : RootedForest) : R :=
  f (ForestAlgebra.ofForest (R := R) φ)

@[simp]
theorem evalForest_counit (φ : RootedForest) :
    evalForest (counit R) φ = ForestAlgebra.counitCoeff (R := R) φ := by
  simp [evalForest, counit]

@[simp]
theorem evalForest_ofCharacter (χ : ForestAlgebra.Character R) (φ : RootedForest) :
    evalForest (ofCharacter χ) φ = χ.evalForest φ :=
  rfl

/-- Compose a linear functional with the recursive antipode. -/
def compAntipode {R : Type u} [CommRing R]
    (f : ForestAlgebra.LinearFunctional R) :
    ForestAlgebra.LinearFunctional R :=
  f.comp (ForestAlgebra.antipode (R := R))

/-- Compose a linear functional with the right-recursive antipode. -/
def compRightAntipode {R : Type u} [CommRing R]
    (f : ForestAlgebra.LinearFunctional R) :
    ForestAlgebra.LinearFunctional R :=
  f.comp (ForestAlgebra.rightAntipode (R := R))

/-- Convolution of linear functionals induced by the BCK coproduct. -/
def convolution (f g : ForestAlgebra.LinearFunctional R) :
    ForestAlgebra.LinearFunctional R :=
  (ForestTensorAlgebra.evalByLinearMaps f g).comp
    (ForestAlgebra.coproduct R).toLinearMap

@[simp]
theorem convolution_ofForest
    (f g : ForestAlgebra.LinearFunctional R) (φ : RootedForest) :
    convolution f g (ForestAlgebra.ofForest (R := R) φ) =
      ((RootedForest.coproductTerms φ).map fun term =>
        f (ForestAlgebra.ofForest (R := R) term.1) *
          g (ForestAlgebra.ofForest (R := R) term.2)).sum := by
  simp [convolution, ForestAlgebra.coproduct_ofForest,
    RootedForest.coproduct_eq_sumTerms_coproductTerms,
    ForestTensorAlgebra.evalByLinearMaps_sumTerms]

@[simp]
theorem evalForest_convolution
    (f g : ForestAlgebra.LinearFunctional R) (φ : RootedForest) :
    evalForest (convolution f g) φ =
      ((RootedForest.coproductTerms φ).map fun term =>
        evalForest f term.1 * evalForest g term.2).sum := by
  simp [evalForest]

@[simp]
theorem evalForest_smul (c : R) (f : ForestAlgebra.LinearFunctional R)
    (φ : RootedForest) :
    evalForest (c • f) φ = c * evalForest f φ :=
  rfl

@[simp]
theorem evalForest_sum (fs : List (ForestAlgebra.LinearFunctional R))
    (φ : RootedForest) :
    evalForest fs.sum φ = (fs.map fun f => evalForest f φ).sum := by
  induction fs with
  | nil =>
      rfl
  | cons f fs ih =>
      change f (ForestAlgebra.ofForest (R := R) φ) +
          fs.sum (ForestAlgebra.ofForest (R := R) φ) =
        f (ForestAlgebra.ofForest (R := R) φ) +
          (fs.map fun f => f (ForestAlgebra.ofForest (R := R) φ)).sum
      have ih' :
          fs.sum (ForestAlgebra.ofForest (R := R) φ) =
            (fs.map fun f => f (ForestAlgebra.ofForest (R := R) φ)).sum := by
        simpa [evalForest] using ih
      rw [ih']

/-- Linear functionals agreeing on every forest monomial are equal. -/
theorem ext_evalForest {f g : ForestAlgebra.LinearFunctional R}
    (h : ∀ φ, evalForest f φ = evalForest g φ) : f = g := by
  refine AddMonoidAlgebra.lhom_ext' fun φ => LinearMap.ext_ring ?_
  exact h φ

/-- Two forest linear functionals agree on all forests of order at most `n`. -/
def AgreeUpToOrder (f g : ForestAlgebra.LinearFunctional R) (n : Nat) : Prop :=
  ∀ φ, RootedForest.order φ ≤ n → evalForest f φ = evalForest g φ

theorem agreeUpToOrder_refl (f : ForestAlgebra.LinearFunctional R) (n : Nat) :
    AgreeUpToOrder f f n := by
  intro φ hφ
  rfl

theorem AgreeUpToOrder.symm {f g : ForestAlgebra.LinearFunctional R} {n : Nat}
    (h : AgreeUpToOrder f g n) : AgreeUpToOrder g f n := by
  intro φ hφ
  exact (h φ hφ).symm

theorem AgreeUpToOrder.trans
    {f g h : ForestAlgebra.LinearFunctional R} {n : Nat}
    (hfg : AgreeUpToOrder f g n) (hgh : AgreeUpToOrder g h n) :
    AgreeUpToOrder f h n := by
  intro φ hφ
  exact (hfg φ hφ).trans (hgh φ hφ)

theorem AgreeUpToOrder.mono {f g : ForestAlgebra.LinearFunctional R} {m n : Nat}
    (h : AgreeUpToOrder f g n) (hmn : m ≤ n) : AgreeUpToOrder f g m := by
  intro φ hφ
  exact h φ (hφ.trans hmn)

theorem AgreeUpToOrder.convolution
    {f f' g g' : ForestAlgebra.LinearFunctional R} {n : Nat}
    (hf : AgreeUpToOrder f f' n) (hg : AgreeUpToOrder g g' n) :
    AgreeUpToOrder (convolution f g) (convolution f' g') n := by
  intro φ hφ
  rw [evalForest_convolution, evalForest_convolution]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term hterm
  have horder := RootedForest.coproductTerms_order hterm
  have hsum : RootedForest.order term.1 + RootedForest.order term.2 ≤ n := by
    rw [horder]
    exact hφ
  have hleft : RootedForest.order term.1 ≤ n :=
    (Nat.le_add_right _ _).trans hsum
  have hright : RootedForest.order term.2 ≤ n :=
    (Nat.le_add_left _ _).trans hsum
  rw [hf term.1 hleft, hg term.2 hright]

end

end LinearFunctional

end ForestAlgebra

namespace ForestTripleTensorAlgebra

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- Evaluate a triple tensor-coded forest term by three linear functionals. -/
def evalByLinearMaps
    (f g h : ForestAlgebra.LinearFunctional R) :
    ForestTripleTensorAlgebra R →ₗ[R] R :=
  (Finsupp.linearCombination R fun term : RootedForest × RootedForest × RootedForest =>
    f (ForestAlgebra.ofForest (R := R) term.1) *
      g (ForestAlgebra.ofForest (R := R) term.2.1) *
        h (ForestAlgebra.ofForest (R := R) term.2.2)).comp
          (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem evalByLinearMaps_ofTriple
    (f g h : ForestAlgebra.LinearFunctional R)
    (term : RootedForest × RootedForest × RootedForest) :
    evalByLinearMaps f g h (ofTriple (R := R) term) =
      f (ForestAlgebra.ofForest (R := R) term.1) *
        g (ForestAlgebra.ofForest (R := R) term.2.1) *
          h (ForestAlgebra.ofForest (R := R) term.2.2) := by
  rw [evalByLinearMaps, ofTriple]
  change (Finsupp.linearCombination R fun term : RootedForest × RootedForest × RootedForest =>
      f (ForestAlgebra.ofForest (R := R) term.1) *
        g (ForestAlgebra.ofForest (R := R) term.2.1) *
          h (ForestAlgebra.ofForest (R := R) term.2.2))
      (Finsupp.single term (1 : R)) =
    f (ForestAlgebra.ofForest (R := R) term.1) *
      g (ForestAlgebra.ofForest (R := R) term.2.1) *
        h (ForestAlgebra.ofForest (R := R) term.2.2)
  rw [Finsupp.linearCombination_single]
  simp

theorem evalByLinearMaps_sumTerms
    (f g h : ForestAlgebra.LinearFunctional R)
    (terms : List (RootedForest × RootedForest × RootedForest)) :
    evalByLinearMaps f g h (sumTerms (R := R) terms) =
      (terms.map fun term =>
        f (ForestAlgebra.ofForest (R := R) term.1) *
          g (ForestAlgebra.ofForest (R := R) term.2.1) *
            h (ForestAlgebra.ofForest (R := R) term.2.2)).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, evalByLinearMaps_ofTriple, ih]
      rfl

private theorem evalByLinearMaps_coproductLeftTerm
    (f g h : ForestAlgebra.LinearFunctional R)
    (term : RootedForest × RootedForest) :
    evalByLinearMaps f g h (sumTerms (R := R) (coproductLeftTerm term)) =
      ForestTensorAlgebra.evalByLinearMaps
        (ForestAlgebra.LinearFunctional.convolution f g) h
        (ForestTensorAlgebra.ofPair (R := R) term) := by
  rw [evalByLinearMaps_sumTerms, ForestTensorAlgebra.evalByLinearMaps_ofPair,
    ForestAlgebra.LinearFunctional.convolution_ofForest, coproductLeftTerm]
  induction RootedForest.coproductTerms term.1 with
  | nil =>
      simp
  | cons left terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul]
      rw [← ih]

private theorem evalByLinearMaps_coproductRightTerm
    (f g h : ForestAlgebra.LinearFunctional R)
    (term : RootedForest × RootedForest) :
    evalByLinearMaps f g h (sumTerms (R := R) (coproductRightTerm term)) =
      ForestTensorAlgebra.evalByLinearMaps
        f (ForestAlgebra.LinearFunctional.convolution g h)
        (ForestTensorAlgebra.ofPair (R := R) term) := by
  rw [evalByLinearMaps_sumTerms, ForestTensorAlgebra.evalByLinearMaps_ofPair,
    ForestAlgebra.LinearFunctional.convolution_ofForest, coproductRightTerm]
  induction RootedForest.coproductTerms term.2 with
  | nil =>
      simp
  | cons right terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add]
      rw [← ih]
      simp [mul_assoc]

theorem evalByLinearMaps_coproductLeft
    (f g h : ForestAlgebra.LinearFunctional R) (x : ForestTensorAlgebra R) :
    evalByLinearMaps f g h (coproductLeft (R := R) x) =
      ForestTensorAlgebra.evalByLinearMaps
        (ForestAlgebra.LinearFunctional.convolution f g) h x := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      evalByLinearMaps f g h (coproductLeft (R := R) x) =
        ForestTensorAlgebra.evalByLinearMaps
          (ForestAlgebra.LinearFunctional.convolution f g) h x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps f g h
          (coproductLeft (R := R) (ForestTensorAlgebra.ofPair (R := R) term)) =
        ForestTensorAlgebra.evalByLinearMaps
          (ForestAlgebra.LinearFunctional.convolution f g) h
          (ForestTensorAlgebra.ofPair (R := R) term)
    rw [← sumTerms_coproductLeftTerm, evalByLinearMaps_coproductLeftTerm]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy
  · intro r x hx
    simpa [map_smul] using congrArg (fun a => r • a) hx

theorem evalByLinearMaps_coproductRight
    (f g h : ForestAlgebra.LinearFunctional R) (x : ForestTensorAlgebra R) :
    evalByLinearMaps f g h (coproductRight (R := R) x) =
      ForestTensorAlgebra.evalByLinearMaps
        f (ForestAlgebra.LinearFunctional.convolution g h) x := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      evalByLinearMaps f g h (coproductRight (R := R) x) =
        ForestTensorAlgebra.evalByLinearMaps
          f (ForestAlgebra.LinearFunctional.convolution g h) x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps f g h
          (coproductRight (R := R) (ForestTensorAlgebra.ofPair (R := R) term)) =
        ForestTensorAlgebra.evalByLinearMaps
          f (ForestAlgebra.LinearFunctional.convolution g h)
          (ForestTensorAlgebra.ofPair (R := R) term)
    rw [← sumTerms_coproductRightTerm, evalByLinearMaps_coproductRightTerm]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy
  · intro r x hx
    simpa [map_smul] using congrArg (fun a => r • a) hx

end

end ForestTripleTensorAlgebra

namespace ForestAlgebra

namespace LinearFunctional

noncomputable section

variable {R : Type u} [CommSemiring R]

private theorem evalByLinearMaps_counit_left
    (f : ForestAlgebra.LinearFunctional R) :
    ForestTensorAlgebra.evalByLinearMaps (counit R) f =
      f.comp (ForestTensorAlgebra.counitLeft (R := R)).toLinearMap := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      ForestTensorAlgebra.evalByLinearMaps (counit R) f x =
        (f.comp (ForestTensorAlgebra.counitLeft (R := R)).toLinearMap) x) x ?_ ?_ ?_
  · intro term
    change
      ForestTensorAlgebra.evalByLinearMaps (counit R) f
          (ForestTensorAlgebra.ofPair (R := R) term) =
        f (ForestTensorAlgebra.counitLeft (R := R)
          (ForestTensorAlgebra.ofPair (R := R) term))
    simp [counit]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

private theorem evalByLinearMaps_counit_right
    (f : ForestAlgebra.LinearFunctional R) :
    ForestTensorAlgebra.evalByLinearMaps f (counit R) =
      f.comp (ForestTensorAlgebra.counitRight (R := R)).toLinearMap := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      ForestTensorAlgebra.evalByLinearMaps f (counit R) x =
        (f.comp (ForestTensorAlgebra.counitRight (R := R)).toLinearMap) x) x ?_ ?_ ?_
  · intro term
    change
      ForestTensorAlgebra.evalByLinearMaps f (counit R)
          (ForestTensorAlgebra.ofPair (R := R) term) =
        f (ForestTensorAlgebra.counitRight (R := R)
          (ForestTensorAlgebra.ofPair (R := R) term))
    simp [counit, mul_comm]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

@[simp]
theorem convolution_counit_left
    (f : ForestAlgebra.LinearFunctional R) :
    convolution (counit R) f = f := by
  apply LinearMap.ext
  intro x
  change
    ForestTensorAlgebra.evalByLinearMaps (counit R) f
        (ForestAlgebra.coproduct R x) = f x
  rw [evalByLinearMaps_counit_left]
  change
    f (ForestTensorAlgebra.counitLeft (R := R)
        (ForestAlgebra.coproduct R x)) = f x
  have h :=
    congrArg (fun F : ForestAlgebra R →ₐ[R] ForestAlgebra R => F x)
      (ForestAlgebra.counitLeft_coproduct (R := R))
  simpa [AlgHom.comp_apply] using congrArg f h

@[simp]
theorem convolution_counit_right
    (f : ForestAlgebra.LinearFunctional R) :
    convolution f (counit R) = f := by
  apply LinearMap.ext
  intro x
  change
    ForestTensorAlgebra.evalByLinearMaps f (counit R)
        (ForestAlgebra.coproduct R x) = f x
  rw [evalByLinearMaps_counit_right]
  change
    f (ForestTensorAlgebra.counitRight (R := R)
        (ForestAlgebra.coproduct R x)) = f x
  have h :=
    congrArg (fun F : ForestAlgebra R →ₐ[R] ForestAlgebra R => F x)
      (ForestAlgebra.counitRight_coproduct (R := R))
  simpa [AlgHom.comp_apply] using congrArg f h

@[simp]
theorem convolution_zero_left
    (f : ForestAlgebra.LinearFunctional R) :
    convolution 0 f = 0 := by
  apply LinearMap.ext
  intro x
  exact AddMonoidAlgebra.induction_on (x := x)
    (motive := fun y : ForestAlgebra R => convolution 0 f y = 0)
    (by
      intro φ
      change convolution 0 f (ForestAlgebra.ofForest (R := R) φ) = 0
      rw [convolution_ofForest]
      simp)
    (by
      intro x y hx hy
      rw [map_add, hx, hy]
      simp)
    (by
      intro r x hx
      rw [map_smul, hx]
      simp)

@[simp]
theorem convolution_zero_right
    (f : ForestAlgebra.LinearFunctional R) :
    convolution f 0 = 0 := by
  apply LinearMap.ext
  intro x
  exact AddMonoidAlgebra.induction_on (x := x)
    (motive := fun y : ForestAlgebra R => convolution f 0 y = 0)
    (by
      intro φ
      change convolution f 0 (ForestAlgebra.ofForest (R := R) φ) = 0
      rw [convolution_ofForest]
      simp)
    (by
      intro x y hx hy
      rw [map_add, hx, hy]
      simp)
    (by
      intro r x hx
      rw [map_smul, hx]
      simp)

theorem convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : ForestAlgebra R,
      ForestAlgebra.coproductLeft R x = ForestAlgebra.coproductRight R x)
    (f g h : ForestAlgebra.LinearFunctional R) :
    convolution (convolution f g) h = convolution f (convolution g h) := by
  apply LinearMap.ext
  intro x
  change
    ForestTensorAlgebra.evalByLinearMaps (convolution f g) h
        (ForestAlgebra.coproduct R x) =
      ForestTensorAlgebra.evalByLinearMaps f (convolution g h)
        (ForestAlgebra.coproduct R x)
  rw [← ForestTripleTensorAlgebra.evalByLinearMaps_coproductLeft,
    ← ForestTripleTensorAlgebra.evalByLinearMaps_coproductRight]
  change
    ForestTripleTensorAlgebra.evalByLinearMaps f g h
        (ForestAlgebra.coproductLeft R x) =
      ForestTripleTensorAlgebra.evalByLinearMaps f g h
        (ForestAlgebra.coproductRight R x)
  rw [hcoassoc x]

theorem convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc : ForestAlgebra.coproductLeft R = ForestAlgebra.coproductRight R)
    (f g h : ForestAlgebra.LinearFunctional R) :
    convolution (convolution f g) h = convolution f (convolution g h) :=
  convolution_assoc_of_coproduct_eq (fun x => by rw [hcoassoc]) f g h

theorem convolution_assoc
    (f g h : ForestAlgebra.LinearFunctional R) :
    convolution (convolution f g) h = convolution f (convolution g h) :=
  convolution_assoc_of_coproductLeft_eq_coproductRight
    (ForestAlgebra.coproductLeft_eq_coproductRight (R := R)) f g h

/-- Convolution powers of a linear functional, with the counit as the zeroth power. -/
def convolutionPower (f : ForestAlgebra.LinearFunctional R) :
    Nat → ForestAlgebra.LinearFunctional R
  | 0 => counit R
  | n + 1 => convolution f (convolutionPower f n)

@[simp]
theorem convolutionPower_zero (f : ForestAlgebra.LinearFunctional R) :
    convolutionPower f 0 = counit R :=
  rfl

@[simp]
theorem convolutionPower_succ (f : ForestAlgebra.LinearFunctional R) (n : Nat) :
    convolutionPower f (n + 1) = convolution f (convolutionPower f n) :=
  rfl

@[simp]
theorem convolutionPower_one (f : ForestAlgebra.LinearFunctional R) :
    convolutionPower f 1 = f := by
  simp [convolutionPower]

theorem convolutionPower_add (f : ForestAlgebra.LinearFunctional R) (m n : Nat) :
    convolutionPower f (m + n) =
      convolution (convolutionPower f m) (convolutionPower f n) := by
  induction m with
  | zero =>
      simp [convolutionPower]
  | succ m ih =>
      simp only [Nat.succ_add, convolutionPower_succ]
      rw [ih, ← convolution_assoc]

theorem convolutionPower_succ_right (f : ForestAlgebra.LinearFunctional R) (n : Nat) :
    convolutionPower f (n + 1) = convolution (convolutionPower f n) f := by
  rw [show n + 1 = n + 1 by rfl, convolutionPower_add]
  simp

@[simp]
theorem convolutionPower_zero_succ (n : Nat) :
    convolutionPower (0 : ForestAlgebra.LinearFunctional R) (n + 1) = 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [convolutionPower_succ, ih]
      simp

theorem convolutionPower_counit (n : Nat) :
    convolutionPower (counit R) n = counit R := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [ih]

theorem AgreeUpToOrder.convolutionPower
    {f g : ForestAlgebra.LinearFunctional R} {n : Nat}
    (h : AgreeUpToOrder f g n) (k : Nat) :
    AgreeUpToOrder (convolutionPower f k) (convolutionPower g k) n := by
  induction k with
  | zero =>
      exact agreeUpToOrder_refl (counit R) n
  | succ k ih =>
      simpa [convolutionPower] using h.convolution ih

/-- The augmentation part of a forest character, viewed as a linear functional. -/
def augmentationPart {R : Type u} [CommRing R] (χ : ForestAlgebra.Character R) :
    ForestAlgebra.LinearFunctional R :=
  ofCharacter χ - counit R

@[simp]
theorem augmentationPart_eval_empty
    {R : Type u} [CommRing R] (χ : ForestAlgebra.Character R) :
    evalForest (augmentationPart χ) RootedForest.empty = 0 := by
  simp [augmentationPart, evalForest, ofCharacter, counit]

theorem agreeUpToOrder_augmentationPart
    {R : Type u} [CommRing R] {χ ψ : ForestAlgebra.Character R} {n : Nat}
    (h : ∀ φ, RootedForest.order φ ≤ n → χ.evalForest φ = ψ.evalForest φ) :
    AgreeUpToOrder (augmentationPart χ) (augmentationPart ψ) n := by
  intro φ hφ
  simp [augmentationPart, evalForest, ofCharacter, counit]
  simpa [ForestAlgebra.Character.evalForest] using h φ hφ

/-- The truncated convolution logarithm of a forest character. -/
def logCharacterTruncated {R : Type u} [Field R]
    (χ : ForestAlgebra.Character R) (n : Nat) :
    ForestAlgebra.LinearFunctional R :=
  ((List.range n).map fun i =>
    let k : Nat := i + 1
    (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) •
      convolutionPower (augmentationPart χ) k).sum

@[simp]
theorem logCharacterTruncated_zero
    {R : Type u} [Field R] (χ : ForestAlgebra.Character R) :
    logCharacterTruncated χ 0 = 0 := by
  simp [logCharacterTruncated]

theorem logCharacterTruncated_evalForest
    {R : Type u} [Field R] (χ : ForestAlgebra.Character R) (n : Nat)
    (φ : RootedForest) :
    evalForest (logCharacterTruncated χ n) φ =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          evalForest (convolutionPower (augmentationPart χ) k) φ).sum := by
  unfold logCharacterTruncated
  rw [evalForest_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  simp [evalForest]

theorem agreeUpToOrder_logCharacterTruncated
    {R : Type u} [Field R] {χ ψ : ForestAlgebra.Character R} {m n : Nat}
    (h : ∀ φ, RootedForest.order φ ≤ n → χ.evalForest φ = ψ.evalForest φ) :
    AgreeUpToOrder (logCharacterTruncated χ m) (logCharacterTruncated ψ m) n := by
  intro φ hφ
  rw [logCharacterTruncated_evalForest, logCharacterTruncated_evalForest]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  dsimp
  have hp :
      evalForest (convolution (augmentationPart χ)
        (convolutionPower (augmentationPart χ) i)) φ =
        evalForest (convolution (augmentationPart ψ)
          (convolutionPower (augmentationPart ψ) i)) φ := by
    simpa [convolutionPower] using
      (agreeUpToOrder_augmentationPart h).convolutionPower (i + 1) φ hφ
  rw [hp]

theorem convolution_compAntipode_ofCharacter_left
    {R : Type u} [CommRing R] (χ : ForestAlgebra.Character R) :
    convolution (compAntipode (ofCharacter χ)) (ofCharacter χ) =
      counit R := by
  apply LinearMap.ext
  intro x
  change
    ForestTensorAlgebra.evalByLinearMaps
        ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
          (ForestAlgebra.antipode (R := R)))
        (χ : ForestAlgebra R →ₐ[R] R).toLinearMap
        (ForestAlgebra.coproduct R x) =
      ForestAlgebra.counit R x
  rw [ForestTensorAlgebra.evalByLinearMaps_compAntipode_ofCharacter]
  exact ForestAlgebra.Character.eval_antipodeLeft_coproduct χ x

theorem convolution_compRightAntipode_ofCharacter_right
    {R : Type u} [CommRing R] (χ : ForestAlgebra.Character R) :
    convolution (ofCharacter χ) (compRightAntipode (ofCharacter χ)) =
      counit R := by
  apply LinearMap.ext
  intro x
  change
    ForestTensorAlgebra.evalByLinearMaps
        (χ : ForestAlgebra R →ₐ[R] R).toLinearMap
        ((χ : ForestAlgebra R →ₐ[R] R).toLinearMap.comp
          (ForestAlgebra.rightAntipode (R := R)))
        (ForestAlgebra.coproduct R x) =
      ForestAlgebra.counit R x
  rw [ForestTensorAlgebra.evalByLinearMaps_compRightAntipode_ofCharacter]
  exact ForestAlgebra.Character.eval_antipodeRight_coproduct χ x

theorem compAntipode_ofCharacter_eq_compRightAntipode
    {R : Type u} [CommRing R] (χ : ForestAlgebra.Character R) :
    compAntipode (ofCharacter χ) = compRightAntipode (ofCharacter χ) := by
  calc
    compAntipode (ofCharacter χ) =
        convolution (compAntipode (ofCharacter χ)) (counit R) := by
          rw [convolution_counit_right]
    _ = convolution (compAntipode (ofCharacter χ))
        (convolution (ofCharacter χ) (compRightAntipode (ofCharacter χ))) := by
          rw [convolution_compRightAntipode_ofCharacter_right χ]
    _ = convolution (convolution (compAntipode (ofCharacter χ)) (ofCharacter χ))
        (compRightAntipode (ofCharacter χ)) := by
          rw [convolution_assoc]
    _ = convolution (counit R) (compRightAntipode (ofCharacter χ)) := by
          rw [convolution_compAntipode_ofCharacter_left χ]
    _ = compRightAntipode (ofCharacter χ) := by
          rw [convolution_counit_left]

end

end LinearFunctional

namespace Character

noncomputable section

variable {R : Type u} [CommRing R]

/-- The antipode-composed linear functional that gives the convolution inverse of a character. -/
def inverseLinearFunctional (χ : ForestAlgebra.Character R) :
    ForestAlgebra.LinearFunctional R :=
  ForestAlgebra.LinearFunctional.compAntipode
    (ForestAlgebra.LinearFunctional.ofCharacter χ)

theorem convolution_inverseLinearFunctional_left (χ : ForestAlgebra.Character R) :
    ForestAlgebra.LinearFunctional.convolution (inverseLinearFunctional χ)
        (ForestAlgebra.LinearFunctional.ofCharacter χ) =
      ForestAlgebra.LinearFunctional.counit R := by
  exact ForestAlgebra.LinearFunctional.convolution_compAntipode_ofCharacter_left χ

theorem convolution_inverseLinearFunctional_right (χ : ForestAlgebra.Character R) :
    ForestAlgebra.LinearFunctional.convolution
        (ForestAlgebra.LinearFunctional.ofCharacter χ) (inverseLinearFunctional χ) =
      ForestAlgebra.LinearFunctional.counit R := by
  rw [inverseLinearFunctional,
    ForestAlgebra.LinearFunctional.compAntipode_ofCharacter_eq_compRightAntipode χ]
  exact ForestAlgebra.LinearFunctional.convolution_compRightAntipode_ofCharacter_right χ

end

end Character

end ForestAlgebra

namespace LForestAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- Linear functionals on the labelled rooted-forest algebra. -/
abbrev LinearFunctional (α : Type u) (R : Type v) [CommSemiring R] :
    Type (max u v) :=
  LForestAlgebra α R →ₗ[R] R

end

end LForestAlgebra

namespace LForestTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- Evaluate a labelled tensor-coded forest pair by two linear functionals. -/
def evalByLinearMaps
    (f g : LForestAlgebra.LinearFunctional α R) :
    LForestTensorAlgebra α R →ₗ[R] R :=
  (Finsupp.linearCombination R fun term : LRootedForest α × LRootedForest α =>
    f (LForestAlgebra.ofForest (R := R) term.1) *
      g (LForestAlgebra.ofForest (R := R) term.2)).comp
        (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem evalByLinearMaps_ofPair
    (f g : LForestAlgebra.LinearFunctional α R)
    (term : LRootedForest α × LRootedForest α) :
    evalByLinearMaps f g (ofPair (R := R) term) =
      f (LForestAlgebra.ofForest (R := R) term.1) *
        g (LForestAlgebra.ofForest (R := R) term.2) := by
  rw [evalByLinearMaps, ofPair]
  change (Finsupp.linearCombination R fun term : LRootedForest α × LRootedForest α =>
      f (LForestAlgebra.ofForest (R := R) term.1) *
        g (LForestAlgebra.ofForest (R := R) term.2))
      (Finsupp.single term (1 : R)) =
    f (LForestAlgebra.ofForest (R := R) term.1) *
      g (LForestAlgebra.ofForest (R := R) term.2)
  rw [Finsupp.linearCombination_single]
  simp

theorem evalByLinearMaps_sumTerms
    (f g : LForestAlgebra.LinearFunctional α R)
    (terms : List (LRootedForest α × LRootedForest α)) :
    evalByLinearMaps f g (sumTerms (R := R) terms) =
      (terms.map fun term =>
        f (LForestAlgebra.ofForest (R := R) term.1) *
          g (LForestAlgebra.ofForest (R := R) term.2)).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, evalByLinearMaps_ofPair, ih]
      rfl

theorem evalByLinearMaps_erase
    (f g : ForestAlgebra.LinearFunctional R) (x : LForestTensorAlgebra α R) :
    ForestTensorAlgebra.evalByLinearMaps f g (erase (R := R) x) =
      evalByLinearMaps
        (f.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap)
        (g.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap) x := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      ForestTensorAlgebra.evalByLinearMaps f g (erase (R := R) x) =
        evalByLinearMaps
          (f.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap)
          (g.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap) x) x ?_ ?_ ?_
  · intro term
    change
      ForestTensorAlgebra.evalByLinearMaps f g
          (erase (R := R) (ofPair (R := R) term)) =
        evalByLinearMaps
          (f.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap)
          (g.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap)
          (ofPair (R := R) term)
    rw [erase_ofPair, ForestTensorAlgebra.evalByLinearMaps_ofPair,
      evalByLinearMaps_ofPair]
    simp [PLTree.eraseCoproductTerm, LinearMap.comp_apply]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy
  · intro c x hx
    rw [show erase (R := R) (c • x) = c • erase (R := R) x by
      ext term
      simp [erase, Finsupp.mapDomain_smul]]
    simp [hx]

theorem evalByLinearMaps_constLabel
    (a : α) (f g : LForestAlgebra.LinearFunctional α R) (x : ForestTensorAlgebra R) :
    evalByLinearMaps f g (constLabel (R := R) a x) =
      ForestTensorAlgebra.evalByLinearMaps
        (f.comp (LForestAlgebra.constLabel a R).toLinearMap)
        (g.comp (LForestAlgebra.constLabel a R).toLinearMap) x := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      evalByLinearMaps f g (constLabel (R := R) a x) =
        ForestTensorAlgebra.evalByLinearMaps
          (f.comp (LForestAlgebra.constLabel a R).toLinearMap)
          (g.comp (LForestAlgebra.constLabel a R).toLinearMap) x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps f g
          (constLabel (R := R) a (ForestTensorAlgebra.ofPair (R := R) term)) =
        ForestTensorAlgebra.evalByLinearMaps
          (f.comp (LForestAlgebra.constLabel a R).toLinearMap)
          (g.comp (LForestAlgebra.constLabel a R).toLinearMap)
          (ForestTensorAlgebra.ofPair (R := R) term)
    rw [constLabel_ofPair, evalByLinearMaps_ofPair,
      ForestTensorAlgebra.evalByLinearMaps_ofPair]
    simp [PLTree.constLabelCoproductTerm, LinearMap.comp_apply]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy
  · intro c x hx
    rw [show constLabel (R := R) a (c • x) = c • constLabel (R := R) a x by
      ext term
      simp [constLabel, Finsupp.mapDomain_smul]]
    simp [hx]

theorem evalByLinearMaps_mapLabels {β : Type w} (labelMap : α → β)
    (f g : LForestAlgebra.LinearFunctional β R) (x : LForestTensorAlgebra α R) :
    LForestTensorAlgebra.evalByLinearMaps f g (mapLabels (R := R) labelMap x) =
      evalByLinearMaps
        (f.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap)
        (g.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap) x := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      LForestTensorAlgebra.evalByLinearMaps f g (mapLabels (R := R) labelMap x) =
        evalByLinearMaps
          (f.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap)
          (g.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap) x) x ?_ ?_ ?_
  · intro term
    change
      LForestTensorAlgebra.evalByLinearMaps f g
          (mapLabels (R := R) labelMap (ofPair (R := R) term)) =
        evalByLinearMaps
          (f.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap)
          (g.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap)
          (ofPair (R := R) term)
    rw [mapLabels_ofPair, LForestTensorAlgebra.evalByLinearMaps_ofPair,
      evalByLinearMaps_ofPair]
    simp [PLTree.mapCoproductTerm, LinearMap.comp_apply]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy
  · intro c x hx
    rw [show mapLabels (R := R) labelMap (c • x) =
        c • mapLabels (R := R) labelMap x by
      ext term
      simp [mapLabels, Finsupp.mapDomain_smul]]
    simp [hx]

theorem evalByLinearMaps_compAntipode_ofCharacter
    {α : Type u} {R : Type v} [CommRing R]
    (χ : LForestAlgebra.Character α R) :
    evalByLinearMaps
        ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
          (LForestAlgebra.antipode (R := R)))
        (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap =
      (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
        (antipodeLeft (R := R)) := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      evalByLinearMaps
          ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
            (LForestAlgebra.antipode (R := R)))
          (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap x =
        ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
          (antipodeLeft (R := R))) x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps
          ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
            (LForestAlgebra.antipode (R := R)))
          (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap
          (ofPair (R := R) term) =
        χ (antipodeLeft (R := R) (ofPair (R := R) term))
    rw [evalByLinearMaps_ofPair, antipodeLeft_ofPair]
    simp [LinearMap.comp_apply]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

theorem evalByLinearMaps_compRightAntipode_ofCharacter
    {α : Type u} {R : Type v} [CommRing R]
    (χ : LForestAlgebra.Character α R) :
    evalByLinearMaps
        (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap
        ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
          (LForestAlgebra.rightAntipode (R := R))) =
      (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
        (antipodeRight (R := R)) := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      evalByLinearMaps
          (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap
          ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
            (LForestAlgebra.rightAntipode (R := R))) x =
        ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
          (antipodeRight (R := R))) x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps
          (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap
          ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
            (LForestAlgebra.rightAntipode (R := R)))
          (ofPair (R := R) term) =
        χ (antipodeRight (R := R) (ofPair (R := R) term))
    rw [evalByLinearMaps_ofPair, antipodeRight_ofPair]
    simp [LinearMap.comp_apply]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

end

end LForestTensorAlgebra

namespace LForestAlgebra

namespace LinearFunctional

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- The labelled counit as a linear functional. -/
def counit (α : Type u) (R : Type v) [CommSemiring R] :
    LForestAlgebra.LinearFunctional α R :=
  (LForestAlgebra.counit α R).toLinearMap

/-- The linear functional underlying a labelled forest-algebra character. -/
def ofCharacter (χ : LForestAlgebra.Character α R) :
    LForestAlgebra.LinearFunctional α R :=
  (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap

/-- Evaluate a labelled linear functional on the monomial associated to a labelled forest. -/
def evalForest (f : LForestAlgebra.LinearFunctional α R) (φ : LRootedForest α) : R :=
  f (LForestAlgebra.ofForest (R := R) φ)

@[simp]
theorem evalForest_counit (φ : LRootedForest α) :
    evalForest (counit α R) φ = LForestAlgebra.counitCoeff (R := R) φ := by
  simp [evalForest, counit]

@[simp]
theorem evalForest_ofCharacter
    (χ : LForestAlgebra.Character α R) (φ : LRootedForest α) :
    evalForest (ofCharacter χ) φ = χ.evalForest φ :=
  rfl

/-- Pull a labelled linear functional back along a relabelling map. -/
def comapMapLabels {β : Type w} (f : α → β)
    (ℓ : LForestAlgebra.LinearFunctional β R) :
    LForestAlgebra.LinearFunctional α R :=
  ℓ.comp (LForestAlgebra.mapLabels (R := R) f).toLinearMap

@[simp]
theorem evalForest_comapMapLabels {β : Type w} (f : α → β)
    (ℓ : LForestAlgebra.LinearFunctional β R) (φ : LRootedForest α) :
    evalForest (comapMapLabels f ℓ) φ =
      evalForest ℓ (LRootedForest.mapLabels f φ) := by
  simp [evalForest, comapMapLabels]

@[simp]
theorem comapMapLabels_zero {β : Type w} (f : α → β) :
    comapMapLabels f (0 : LForestAlgebra.LinearFunctional β R) = 0 := by
  ext x
  rfl

@[simp]
theorem comapMapLabels_add {β : Type w} (f : α → β)
    (ℓ m : LForestAlgebra.LinearFunctional β R) :
    comapMapLabels f (ℓ + m) = comapMapLabels f ℓ + comapMapLabels f m := by
  ext x
  rfl

@[simp]
theorem comapMapLabels_smul {β : Type w} (f : α → β)
    (c : R) (ℓ : LForestAlgebra.LinearFunctional β R) :
    comapMapLabels f (c • ℓ) = c • comapMapLabels f ℓ := by
  ext x
  rfl

theorem comapMapLabels_sum {β : Type w} (f : α → β)
    (ℓs : List (LForestAlgebra.LinearFunctional β R)) :
    comapMapLabels f ℓs.sum = (ℓs.map (comapMapLabels f)).sum := by
  induction ℓs with
  | nil =>
      simp
  | cons ℓ ℓs ih =>
      simp [ih]

/-- Pull an unlabelled linear functional back by forgetting labels. -/
def comapEraseLabels (ℓ : ForestAlgebra.LinearFunctional R) :
    LForestAlgebra.LinearFunctional α R :=
  ℓ.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap

@[simp]
theorem evalForest_comapEraseLabels
    (ℓ : ForestAlgebra.LinearFunctional R) (φ : LRootedForest α) :
    evalForest (comapEraseLabels (α := α) ℓ) φ =
      ForestAlgebra.LinearFunctional.evalForest ℓ (LRootedForest.erase φ) := by
  simp [evalForest, comapEraseLabels, ForestAlgebra.LinearFunctional.evalForest]

@[simp]
theorem comapEraseLabels_zero :
    comapEraseLabels (α := α) (0 : ForestAlgebra.LinearFunctional R) = 0 := by
  ext x
  rfl

@[simp]
theorem comapEraseLabels_add
    (ℓ m : ForestAlgebra.LinearFunctional R) :
    comapEraseLabels (α := α) (ℓ + m) =
      comapEraseLabels ℓ + comapEraseLabels m := by
  ext x
  rfl

@[simp]
theorem comapEraseLabels_smul
    (c : R) (ℓ : ForestAlgebra.LinearFunctional R) :
    comapEraseLabels (α := α) (c • ℓ) =
      c • comapEraseLabels ℓ := by
  ext x
  rfl

theorem comapEraseLabels_sum
    (ℓs : List (ForestAlgebra.LinearFunctional R)) :
    comapEraseLabels (α := α) ℓs.sum = (ℓs.map comapEraseLabels).sum := by
  induction ℓs with
  | nil =>
      simp
  | cons ℓ ℓs ih =>
      simp [ih]

/-- Pull a labelled linear functional back along constant labelling. -/
def comapConstLabel (a : α) (ℓ : LForestAlgebra.LinearFunctional α R) :
    ForestAlgebra.LinearFunctional R :=
  ℓ.comp (LForestAlgebra.constLabel a R).toLinearMap

@[simp]
theorem evalForest_comapConstLabel
    (a : α) (ℓ : LForestAlgebra.LinearFunctional α R) (φ : RootedForest) :
    ForestAlgebra.LinearFunctional.evalForest (comapConstLabel a ℓ) φ =
      evalForest ℓ (LRootedForest.constLabel a φ) := by
  simp [ForestAlgebra.LinearFunctional.evalForest, evalForest, comapConstLabel]

@[simp]
theorem comapConstLabel_zero (a : α) :
    comapConstLabel a (0 : LForestAlgebra.LinearFunctional α R) = 0 := by
  ext x
  rfl

@[simp]
theorem comapConstLabel_add (a : α)
    (ℓ m : LForestAlgebra.LinearFunctional α R) :
    comapConstLabel a (ℓ + m) =
      comapConstLabel a ℓ + comapConstLabel a m := by
  ext x
  rfl

@[simp]
theorem comapConstLabel_smul (a : α)
    (c : R) (ℓ : LForestAlgebra.LinearFunctional α R) :
    comapConstLabel a (c • ℓ) =
      c • comapConstLabel a ℓ := by
  ext x
  rfl

theorem comapConstLabel_sum (a : α)
    (ℓs : List (LForestAlgebra.LinearFunctional α R)) :
    comapConstLabel a ℓs.sum = (ℓs.map (comapConstLabel a)).sum := by
  induction ℓs with
  | nil =>
      simp
  | cons ℓ ℓs ih =>
      simp [ih]

/-- Compose a labelled linear functional with the recursive antipode. -/
def compAntipode {α : Type u} {R : Type v} [CommRing R]
    (f : LForestAlgebra.LinearFunctional α R) :
    LForestAlgebra.LinearFunctional α R :=
  f.comp (LForestAlgebra.antipode (R := R))

/-- Compose a labelled linear functional with the right-recursive antipode. -/
def compRightAntipode {α : Type u} {R : Type v} [CommRing R]
    (f : LForestAlgebra.LinearFunctional α R) :
    LForestAlgebra.LinearFunctional α R :=
  f.comp (LForestAlgebra.rightAntipode (R := R))

/-- Convolution of labelled linear functionals induced by the labelled BCK coproduct. -/
def convolution (f g : LForestAlgebra.LinearFunctional α R) :
    LForestAlgebra.LinearFunctional α R :=
  (LForestTensorAlgebra.evalByLinearMaps f g).comp
    (LForestAlgebra.coproduct α R).toLinearMap

@[simp]
theorem convolution_ofForest
    (f g : LForestAlgebra.LinearFunctional α R) (φ : LRootedForest α) :
    convolution f g (LForestAlgebra.ofForest (R := R) φ) =
      ((LRootedForest.coproductTerms φ).map fun term =>
        f (LForestAlgebra.ofForest (R := R) term.1) *
          g (LForestAlgebra.ofForest (R := R) term.2)).sum := by
  simp [convolution, LForestAlgebra.coproduct_ofForest,
    LRootedForest.coproduct_eq_sumTerms_coproductTerms,
    LForestTensorAlgebra.evalByLinearMaps_sumTerms]

@[simp]
theorem evalForest_convolution
    (f g : LForestAlgebra.LinearFunctional α R) (φ : LRootedForest α) :
    evalForest (convolution f g) φ =
      ((LRootedForest.coproductTerms φ).map fun term =>
        evalForest f term.1 * evalForest g term.2).sum := by
  simp [evalForest]

@[simp]
theorem evalForest_smul (c : R) (f : LForestAlgebra.LinearFunctional α R)
    (φ : LRootedForest α) :
    evalForest (c • f) φ = c * evalForest f φ :=
  rfl

@[simp]
theorem evalForest_sum (fs : List (LForestAlgebra.LinearFunctional α R))
    (φ : LRootedForest α) :
    evalForest fs.sum φ = (fs.map fun f => evalForest f φ).sum := by
  induction fs with
  | nil =>
      rfl
  | cons f fs ih =>
      change f (LForestAlgebra.ofForest (R := R) φ) +
          fs.sum (LForestAlgebra.ofForest (R := R) φ) =
        f (LForestAlgebra.ofForest (R := R) φ) +
          (fs.map fun f => f (LForestAlgebra.ofForest (R := R) φ)).sum
      have ih' :
          fs.sum (LForestAlgebra.ofForest (R := R) φ) =
            (fs.map fun f => f (LForestAlgebra.ofForest (R := R) φ)).sum := by
        simpa [evalForest] using ih
      rw [ih']

/-- Two labelled forest linear functionals agree on all forests of order at most `n`. -/
def AgreeUpToOrder (f g : LForestAlgebra.LinearFunctional α R) (n : Nat) : Prop :=
  ∀ φ, LRootedForest.order φ ≤ n → evalForest f φ = evalForest g φ

theorem agreeUpToOrder_refl (f : LForestAlgebra.LinearFunctional α R) (n : Nat) :
    AgreeUpToOrder f f n := by
  intro φ hφ
  rfl

theorem AgreeUpToOrder.symm {f g : LForestAlgebra.LinearFunctional α R} {n : Nat}
    (h : AgreeUpToOrder f g n) : AgreeUpToOrder g f n := by
  intro φ hφ
  exact (h φ hφ).symm

theorem AgreeUpToOrder.trans
    {f g h : LForestAlgebra.LinearFunctional α R} {n : Nat}
    (hfg : AgreeUpToOrder f g n) (hgh : AgreeUpToOrder g h n) :
    AgreeUpToOrder f h n := by
  intro φ hφ
  exact (hfg φ hφ).trans (hgh φ hφ)

theorem AgreeUpToOrder.mono
    {f g : LForestAlgebra.LinearFunctional α R} {m n : Nat}
    (h : AgreeUpToOrder f g n) (hmn : m ≤ n) : AgreeUpToOrder f g m := by
  intro φ hφ
  exact h φ (hφ.trans hmn)

theorem AgreeUpToOrder.convolution
    {f f' g g' : LForestAlgebra.LinearFunctional α R} {n : Nat}
    (hf : AgreeUpToOrder f f' n) (hg : AgreeUpToOrder g g' n) :
    AgreeUpToOrder (convolution f g) (convolution f' g') n := by
  intro φ hφ
  rw [evalForest_convolution, evalForest_convolution]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term hterm
  have horder := LRootedForest.coproductTerms_order hterm
  have hsum : LRootedForest.order term.1 + LRootedForest.order term.2 ≤ n := by
    rw [horder]
    exact hφ
  have hleft : LRootedForest.order term.1 ≤ n :=
    (Nat.le_add_right _ _).trans hsum
  have hright : LRootedForest.order term.2 ≤ n :=
    (Nat.le_add_left _ _).trans hsum
  rw [hf term.1 hleft, hg term.2 hright]

theorem convolution_comp_eraseLabels
    (f g : ForestAlgebra.LinearFunctional R) :
    (ForestAlgebra.LinearFunctional.convolution f g).comp
        (LForestAlgebra.eraseLabels (α := α) R).toLinearMap =
      convolution
        (f.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap)
        (g.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap) := by
  apply LinearMap.ext
  intro x
  change
    ForestTensorAlgebra.evalByLinearMaps f g
        (ForestAlgebra.coproduct R
          (LForestAlgebra.eraseLabels (α := α) R x)) =
      LForestTensorAlgebra.evalByLinearMaps
        (f.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap)
        (g.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap)
        (LForestAlgebra.coproduct α R x)
  rw [← LForestAlgebra.eraseLabels_coproduct,
    LForestTensorAlgebra.evalByLinearMaps_erase]

theorem convolution_comp_constLabel
    (a : α) (f g : LForestAlgebra.LinearFunctional α R) :
    (convolution f g).comp (LForestAlgebra.constLabel a R).toLinearMap =
      ForestAlgebra.LinearFunctional.convolution
        (f.comp (LForestAlgebra.constLabel a R).toLinearMap)
        (g.comp (LForestAlgebra.constLabel a R).toLinearMap) := by
  apply LinearMap.ext
  intro x
  change
    LForestTensorAlgebra.evalByLinearMaps f g
        (LForestAlgebra.coproduct α R (LForestAlgebra.constLabel a R x)) =
      ForestTensorAlgebra.evalByLinearMaps
        (f.comp (LForestAlgebra.constLabel a R).toLinearMap)
        (g.comp (LForestAlgebra.constLabel a R).toLinearMap)
        (ForestAlgebra.coproduct R x)
  rw [← LForestAlgebra.constLabel_coproduct,
    LForestTensorAlgebra.evalByLinearMaps_constLabel]

theorem convolution_comp_mapLabels {β : Type w} (labelMap : α → β)
    (f g : LForestAlgebra.LinearFunctional β R) :
    (convolution f g).comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap =
      convolution
        (f.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap)
        (g.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap) := by
  apply LinearMap.ext
  intro x
  change
    LForestTensorAlgebra.evalByLinearMaps f g
        (LForestAlgebra.coproduct β R
          (LForestAlgebra.mapLabels (R := R) labelMap x)) =
      LForestTensorAlgebra.evalByLinearMaps
        (f.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap)
        (g.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap)
        (LForestAlgebra.coproduct α R x)
  rw [← LForestAlgebra.mapLabels_coproduct,
    LForestTensorAlgebra.evalByLinearMaps_mapLabels]

theorem comapMapLabels_counit {β : Type w} (f : α → β) :
    comapMapLabels f (counit β R) = counit α R := by
  change
    (LForestAlgebra.Character.comapMapLabels f
        (LForestAlgebra.counit β R)).toLinearMap =
      (LForestAlgebra.counit α R).toLinearMap
  rw [LForestAlgebra.Character.comapMapLabels_counit]

theorem comapMapLabels_ofCharacter {β : Type w} (f : α → β)
    (χ : LForestAlgebra.Character β R) :
    comapMapLabels f (ofCharacter χ) =
      ofCharacter (LForestAlgebra.Character.comapMapLabels f χ) :=
  rfl

theorem comapEraseLabels_counit :
    comapEraseLabels (α := α) (ForestAlgebra.LinearFunctional.counit R) =
      counit α R := by
  change
    (LForestAlgebra.Character.comapEraseLabels (α := α)
        (ForestAlgebra.counit R)).toLinearMap =
      (LForestAlgebra.counit α R).toLinearMap
  rw [LForestAlgebra.Character.comapEraseLabels_counit]

theorem comapEraseLabels_ofCharacter
    (χ : ForestAlgebra.Character R) :
    comapEraseLabels (α := α) (ForestAlgebra.LinearFunctional.ofCharacter χ) =
      ofCharacter (LForestAlgebra.Character.comapEraseLabels (α := α) χ) :=
  rfl

theorem comapConstLabel_counit (a : α) :
    comapConstLabel a (counit α R) =
      ForestAlgebra.LinearFunctional.counit R := by
  change
    (LForestAlgebra.Character.comapConstLabel a
        (LForestAlgebra.counit α R)).toLinearMap =
      (ForestAlgebra.counit R).toLinearMap
  rw [LForestAlgebra.Character.comapConstLabel_counit]

theorem comapConstLabel_ofCharacter
    (a : α) (χ : LForestAlgebra.Character α R) :
    comapConstLabel a (ofCharacter χ) =
      ForestAlgebra.LinearFunctional.ofCharacter
        (LForestAlgebra.Character.comapConstLabel a χ) :=
  rfl

theorem convolution_comapMapLabels {β : Type w} (f : α → β)
    (ℓ m : LForestAlgebra.LinearFunctional β R) :
    convolution (comapMapLabels f ℓ) (comapMapLabels f m) =
      comapMapLabels f (convolution ℓ m) :=
  (convolution_comp_mapLabels f ℓ m).symm

theorem convolution_comapEraseLabels
    (ℓ m : ForestAlgebra.LinearFunctional R) :
    convolution (comapEraseLabels (α := α) ℓ) (comapEraseLabels m) =
      comapEraseLabels (α := α) (ForestAlgebra.LinearFunctional.convolution ℓ m) :=
  (convolution_comp_eraseLabels (α := α) ℓ m).symm

theorem convolution_comapConstLabel
    (a : α) (ℓ m : LForestAlgebra.LinearFunctional α R) :
    ForestAlgebra.LinearFunctional.convolution
        (comapConstLabel a ℓ) (comapConstLabel a m) =
      comapConstLabel a (convolution ℓ m) :=
  (convolution_comp_constLabel a ℓ m).symm

end

end LinearFunctional

end LForestAlgebra

namespace LForestTripleTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- Evaluate a labelled triple tensor term by three linear functionals. -/
def evalByLinearMaps
    (f g h : LForestAlgebra.LinearFunctional α R) :
    LForestTripleTensorAlgebra α R →ₗ[R] R :=
  (Finsupp.linearCombination R fun term : LRootedForest α × LRootedForest α × LRootedForest α =>
    f (LForestAlgebra.ofForest (R := R) term.1) *
      g (LForestAlgebra.ofForest (R := R) term.2.1) *
        h (LForestAlgebra.ofForest (R := R) term.2.2)).comp
          (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem evalByLinearMaps_ofTriple
    (f g h : LForestAlgebra.LinearFunctional α R)
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    evalByLinearMaps f g h (ofTriple (R := R) term) =
      f (LForestAlgebra.ofForest (R := R) term.1) *
        g (LForestAlgebra.ofForest (R := R) term.2.1) *
          h (LForestAlgebra.ofForest (R := R) term.2.2) := by
  rw [evalByLinearMaps, ofTriple]
  change (Finsupp.linearCombination R fun term :
      LRootedForest α × LRootedForest α × LRootedForest α =>
      f (LForestAlgebra.ofForest (R := R) term.1) *
        g (LForestAlgebra.ofForest (R := R) term.2.1) *
          h (LForestAlgebra.ofForest (R := R) term.2.2))
      (Finsupp.single term (1 : R)) =
    f (LForestAlgebra.ofForest (R := R) term.1) *
      g (LForestAlgebra.ofForest (R := R) term.2.1) *
        h (LForestAlgebra.ofForest (R := R) term.2.2)
  rw [Finsupp.linearCombination_single]
  simp

theorem evalByLinearMaps_sumTerms
    (f g h : LForestAlgebra.LinearFunctional α R)
    (terms : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    evalByLinearMaps f g h (sumTerms (R := R) terms) =
      (terms.map fun term =>
        f (LForestAlgebra.ofForest (R := R) term.1) *
          g (LForestAlgebra.ofForest (R := R) term.2.1) *
            h (LForestAlgebra.ofForest (R := R) term.2.2)).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, evalByLinearMaps_ofTriple, ih]
      rfl

private theorem evalByLinearMaps_coproductLeftTerm
    (f g h : LForestAlgebra.LinearFunctional α R)
    (term : LRootedForest α × LRootedForest α) :
    evalByLinearMaps f g h (sumTerms (R := R) (coproductLeftTerm term)) =
      LForestTensorAlgebra.evalByLinearMaps
        (LForestAlgebra.LinearFunctional.convolution f g) h
        (LForestTensorAlgebra.ofPair (R := R) term) := by
  rw [evalByLinearMaps_sumTerms, LForestTensorAlgebra.evalByLinearMaps_ofPair,
    LForestAlgebra.LinearFunctional.convolution_ofForest, coproductLeftTerm]
  induction LRootedForest.coproductTerms term.1 with
  | nil =>
      simp
  | cons left terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul]
      rw [← ih]

private theorem evalByLinearMaps_coproductRightTerm
    (f g h : LForestAlgebra.LinearFunctional α R)
    (term : LRootedForest α × LRootedForest α) :
    evalByLinearMaps f g h (sumTerms (R := R) (coproductRightTerm term)) =
      LForestTensorAlgebra.evalByLinearMaps
        f (LForestAlgebra.LinearFunctional.convolution g h)
        (LForestTensorAlgebra.ofPair (R := R) term) := by
  rw [evalByLinearMaps_sumTerms, LForestTensorAlgebra.evalByLinearMaps_ofPair,
    LForestAlgebra.LinearFunctional.convolution_ofForest, coproductRightTerm]
  induction LRootedForest.coproductTerms term.2 with
  | nil =>
      simp
  | cons right terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add]
      rw [← ih]
      simp [mul_assoc]

theorem evalByLinearMaps_coproductLeft
    (f g h : LForestAlgebra.LinearFunctional α R) (x : LForestTensorAlgebra α R) :
    evalByLinearMaps f g h (coproductLeft (R := R) x) =
      LForestTensorAlgebra.evalByLinearMaps
        (LForestAlgebra.LinearFunctional.convolution f g) h x := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      evalByLinearMaps f g h (coproductLeft (R := R) x) =
        LForestTensorAlgebra.evalByLinearMaps
          (LForestAlgebra.LinearFunctional.convolution f g) h x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps f g h
          (coproductLeft (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
        LForestTensorAlgebra.evalByLinearMaps
          (LForestAlgebra.LinearFunctional.convolution f g) h
          (LForestTensorAlgebra.ofPair (R := R) term)
    rw [← sumTerms_coproductLeftTerm, evalByLinearMaps_coproductLeftTerm]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy
  · intro r x hx
    simpa [map_smul] using congrArg (fun a => r • a) hx

theorem evalByLinearMaps_coproductRight
    (f g h : LForestAlgebra.LinearFunctional α R) (x : LForestTensorAlgebra α R) :
    evalByLinearMaps f g h (coproductRight (R := R) x) =
      LForestTensorAlgebra.evalByLinearMaps
        f (LForestAlgebra.LinearFunctional.convolution g h) x := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      evalByLinearMaps f g h (coproductRight (R := R) x) =
        LForestTensorAlgebra.evalByLinearMaps
          f (LForestAlgebra.LinearFunctional.convolution g h) x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps f g h
          (coproductRight (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
        LForestTensorAlgebra.evalByLinearMaps
          f (LForestAlgebra.LinearFunctional.convolution g h)
          (LForestTensorAlgebra.ofPair (R := R) term)
    rw [← sumTerms_coproductRightTerm, evalByLinearMaps_coproductRightTerm]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy
  · intro r x hx
    simpa [map_smul] using congrArg (fun a => r • a) hx

end

end LForestTripleTensorAlgebra

namespace LForestAlgebra

namespace LinearFunctional

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

private theorem evalByLinearMaps_counit_left
    (f : LForestAlgebra.LinearFunctional α R) :
    LForestTensorAlgebra.evalByLinearMaps (counit α R) f =
      f.comp (LForestTensorAlgebra.counitLeft (R := R)).toLinearMap := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      LForestTensorAlgebra.evalByLinearMaps (counit α R) f x =
        (f.comp (LForestTensorAlgebra.counitLeft (R := R)).toLinearMap) x) x ?_ ?_ ?_
  · intro term
    change
      LForestTensorAlgebra.evalByLinearMaps (counit α R) f
          (LForestTensorAlgebra.ofPair (R := R) term) =
        f (LForestTensorAlgebra.counitLeft (R := R)
          (LForestTensorAlgebra.ofPair (R := R) term))
    rw [LForestTensorAlgebra.evalByLinearMaps_ofPair,
      LForestTensorAlgebra.counitLeft_ofPair]
    simp [counit]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

private theorem evalByLinearMaps_counit_right
    (f : LForestAlgebra.LinearFunctional α R) :
    LForestTensorAlgebra.evalByLinearMaps f (counit α R) =
      f.comp (LForestTensorAlgebra.counitRight (R := R)).toLinearMap := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      LForestTensorAlgebra.evalByLinearMaps f (counit α R) x =
        (f.comp (LForestTensorAlgebra.counitRight (R := R)).toLinearMap) x) x ?_ ?_ ?_
  · intro term
    change
      LForestTensorAlgebra.evalByLinearMaps f (counit α R)
          (LForestTensorAlgebra.ofPair (R := R) term) =
        f (LForestTensorAlgebra.counitRight (R := R)
          (LForestTensorAlgebra.ofPair (R := R) term))
    rw [LForestTensorAlgebra.evalByLinearMaps_ofPair,
      LForestTensorAlgebra.counitRight_ofPair]
    simp [counit, mul_comm]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

@[simp]
theorem convolution_counit_left
    (f : LForestAlgebra.LinearFunctional α R) :
    convolution (counit α R) f = f := by
  apply LinearMap.ext
  intro x
  change
    LForestTensorAlgebra.evalByLinearMaps (counit α R) f
        (LForestAlgebra.coproduct α R x) = f x
  rw [evalByLinearMaps_counit_left]
  change
    f (LForestTensorAlgebra.counitLeft (R := R)
        (LForestAlgebra.coproduct α R x)) = f x
  have h :=
    congrArg (fun F : LForestAlgebra α R →ₐ[R] LForestAlgebra α R => F x)
      (LForestAlgebra.counitLeft_coproduct (α := α) (R := R))
  simpa [AlgHom.comp_apply] using congrArg f h

@[simp]
theorem convolution_counit_right
    (f : LForestAlgebra.LinearFunctional α R) :
    convolution f (counit α R) = f := by
  apply LinearMap.ext
  intro x
  change
    LForestTensorAlgebra.evalByLinearMaps f (counit α R)
        (LForestAlgebra.coproduct α R x) = f x
  rw [evalByLinearMaps_counit_right]
  change
    f (LForestTensorAlgebra.counitRight (R := R)
        (LForestAlgebra.coproduct α R x)) = f x
  have h :=
    congrArg (fun F : LForestAlgebra α R →ₐ[R] LForestAlgebra α R => F x)
      (LForestAlgebra.counitRight_coproduct (α := α) (R := R))
  simpa [AlgHom.comp_apply] using congrArg f h

@[simp]
theorem convolution_zero_left
    (f : LForestAlgebra.LinearFunctional α R) :
    convolution 0 f = 0 := by
  apply LinearMap.ext
  intro x
  exact AddMonoidAlgebra.induction_on (x := x)
    (motive := fun y : LForestAlgebra α R => convolution 0 f y = 0)
    (by
      intro φ
      change convolution 0 f (LForestAlgebra.ofForest (R := R) φ) = 0
      rw [convolution_ofForest]
      simp)
    (by
      intro x y hx hy
      rw [map_add, hx, hy]
      simp)
    (by
      intro r x hx
      rw [map_smul, hx]
      simp)

@[simp]
theorem convolution_zero_right
    (f : LForestAlgebra.LinearFunctional α R) :
    convolution f 0 = 0 := by
  apply LinearMap.ext
  intro x
  exact AddMonoidAlgebra.induction_on (x := x)
    (motive := fun y : LForestAlgebra α R => convolution f 0 y = 0)
    (by
      intro φ
      change convolution f 0 (LForestAlgebra.ofForest (R := R) φ) = 0
      rw [convolution_ofForest]
      simp)
    (by
      intro x y hx hy
      rw [map_add, hx, hy]
      simp)
    (by
      intro r x hx
      rw [map_smul, hx]
      simp)

theorem convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : LForestAlgebra α R,
      LForestAlgebra.coproductLeft α R x = LForestAlgebra.coproductRight α R x)
    (f g h : LForestAlgebra.LinearFunctional α R) :
    convolution (convolution f g) h = convolution f (convolution g h) := by
  apply LinearMap.ext
  intro x
  change
    LForestTensorAlgebra.evalByLinearMaps (convolution f g) h
        (LForestAlgebra.coproduct α R x) =
      LForestTensorAlgebra.evalByLinearMaps f (convolution g h)
        (LForestAlgebra.coproduct α R x)
  rw [← LForestTripleTensorAlgebra.evalByLinearMaps_coproductLeft,
    ← LForestTripleTensorAlgebra.evalByLinearMaps_coproductRight]
  change
    LForestTripleTensorAlgebra.evalByLinearMaps f g h
        (LForestAlgebra.coproductLeft α R x) =
      LForestTripleTensorAlgebra.evalByLinearMaps f g h
        (LForestAlgebra.coproductRight α R x)
  rw [hcoassoc x]

theorem convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc : LForestAlgebra.coproductLeft α R = LForestAlgebra.coproductRight α R)
    (f g h : LForestAlgebra.LinearFunctional α R) :
    convolution (convolution f g) h = convolution f (convolution g h) :=
  convolution_assoc_of_coproduct_eq (fun x => by rw [hcoassoc]) f g h

theorem convolution_assoc
    (f g h : LForestAlgebra.LinearFunctional α R) :
    convolution (convolution f g) h = convolution f (convolution g h) :=
  convolution_assoc_of_coproductLeft_eq_coproductRight
    (LForestAlgebra.coproductLeft_eq_coproductRight (α := α) (R := R)) f g h

/-- Convolution powers of a labelled linear functional, with the counit as zeroth power. -/
def convolutionPower (f : LForestAlgebra.LinearFunctional α R) :
    Nat → LForestAlgebra.LinearFunctional α R
  | 0 => counit α R
  | n + 1 => convolution f (convolutionPower f n)

@[simp]
theorem convolutionPower_zero (f : LForestAlgebra.LinearFunctional α R) :
    convolutionPower f 0 = counit α R :=
  rfl

@[simp]
theorem convolutionPower_succ
    (f : LForestAlgebra.LinearFunctional α R) (n : Nat) :
    convolutionPower f (n + 1) = convolution f (convolutionPower f n) :=
  rfl

@[simp]
theorem convolutionPower_one (f : LForestAlgebra.LinearFunctional α R) :
    convolutionPower f 1 = f := by
  simp [convolutionPower]

theorem convolutionPower_add
    (f : LForestAlgebra.LinearFunctional α R) (m n : Nat) :
    convolutionPower f (m + n) =
      convolution (convolutionPower f m) (convolutionPower f n) := by
  induction m with
  | zero =>
      simp [convolutionPower]
  | succ m ih =>
      simp only [Nat.succ_add, convolutionPower_succ]
      rw [ih, ← convolution_assoc]

theorem convolutionPower_succ_right
    (f : LForestAlgebra.LinearFunctional α R) (n : Nat) :
    convolutionPower f (n + 1) = convolution (convolutionPower f n) f := by
  rw [show n + 1 = n + 1 by rfl, convolutionPower_add]
  simp

@[simp]
theorem convolutionPower_zero_succ (n : Nat) :
    convolutionPower (0 : LForestAlgebra.LinearFunctional α R) (n + 1) = 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [convolutionPower_succ, ih]
      simp

theorem convolutionPower_counit (n : Nat) :
    convolutionPower (counit α R) n = counit α R := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [ih]

theorem AgreeUpToOrder.convolutionPower
    {f g : LForestAlgebra.LinearFunctional α R} {n : Nat}
    (h : AgreeUpToOrder f g n) (k : Nat) :
    AgreeUpToOrder (convolutionPower f k) (convolutionPower g k) n := by
  induction k with
  | zero =>
      exact agreeUpToOrder_refl (counit α R) n
  | succ k ih =>
      simpa [convolutionPower] using h.convolution ih

theorem convolutionPower_comp_eraseLabels
    (f : ForestAlgebra.LinearFunctional R) (n : Nat) :
    (ForestAlgebra.LinearFunctional.convolutionPower f n).comp
        (LForestAlgebra.eraseLabels (α := α) R).toLinearMap =
      convolutionPower
        (f.comp (LForestAlgebra.eraseLabels (α := α) R).toLinearMap) n := by
  induction n with
  | zero =>
      change (ForestAlgebra.counit R).toLinearMap.comp
          (LForestAlgebra.eraseLabels (α := α) R).toLinearMap =
        (LForestAlgebra.counit α R).toLinearMap
      exact congrArg (fun F : LForestAlgebra α R →ₐ[R] R => F.toLinearMap)
        (LForestAlgebra.counit_comp_eraseLabels (α := α) (R := R))
  | succ n ih =>
      rw [ForestAlgebra.LinearFunctional.convolutionPower_succ,
        convolutionPower_succ, convolution_comp_eraseLabels, ih]

theorem convolutionPower_comp_constLabel
    (a : α) (f : LForestAlgebra.LinearFunctional α R) (n : Nat) :
    (convolutionPower f n).comp (LForestAlgebra.constLabel a R).toLinearMap =
      ForestAlgebra.LinearFunctional.convolutionPower
        (f.comp (LForestAlgebra.constLabel a R).toLinearMap) n := by
  induction n with
  | zero =>
      change (LForestAlgebra.counit α R).toLinearMap.comp
          (LForestAlgebra.constLabel a R).toLinearMap =
        (ForestAlgebra.counit R).toLinearMap
      exact congrArg (fun F : ForestAlgebra R →ₐ[R] R => F.toLinearMap)
        (LForestAlgebra.Character.comapConstLabel_counit (R := R) a)
  | succ n ih =>
      rw [convolutionPower_succ, ForestAlgebra.LinearFunctional.convolutionPower_succ,
        convolution_comp_constLabel, ih]

theorem convolutionPower_comp_mapLabels {β : Type w} (labelMap : α → β)
    (f : LForestAlgebra.LinearFunctional β R) (n : Nat) :
    (convolutionPower f n).comp
        (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap =
      convolutionPower
        (f.comp (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap) n := by
  induction n with
  | zero =>
      change (LForestAlgebra.counit β R).toLinearMap.comp
          (LForestAlgebra.mapLabels (R := R) labelMap).toLinearMap =
        (LForestAlgebra.counit α R).toLinearMap
      exact congrArg (fun F : LForestAlgebra α R →ₐ[R] R => F.toLinearMap)
        (LForestAlgebra.counit_comp_mapLabels (R := R) labelMap)
  | succ n ih =>
      rw [convolutionPower_succ, convolutionPower_succ, convolution_comp_mapLabels, ih]

theorem convolutionPower_comapMapLabels {β : Type w} (f : α → β)
    (ℓ : LForestAlgebra.LinearFunctional β R) (n : Nat) :
    convolutionPower (comapMapLabels f ℓ) n =
      comapMapLabels f (convolutionPower ℓ n) :=
  (convolutionPower_comp_mapLabels f ℓ n).symm

theorem convolutionPower_comapEraseLabels
    (ℓ : ForestAlgebra.LinearFunctional R) (n : Nat) :
    convolutionPower (comapEraseLabels (α := α) ℓ) n =
      comapEraseLabels (α := α)
        (ForestAlgebra.LinearFunctional.convolutionPower ℓ n) :=
  (convolutionPower_comp_eraseLabels (α := α) ℓ n).symm

theorem convolutionPower_comapConstLabel
    (a : α) (ℓ : LForestAlgebra.LinearFunctional α R) (n : Nat) :
    ForestAlgebra.LinearFunctional.convolutionPower
        (comapConstLabel a ℓ) n =
      comapConstLabel a (convolutionPower ℓ n) :=
  (convolutionPower_comp_constLabel a ℓ n).symm

/-- The augmentation part of a labelled forest character. -/
def augmentationPart {α : Type u} {R : Type v} [CommRing R]
    (χ : LForestAlgebra.Character α R) :
    LForestAlgebra.LinearFunctional α R :=
  ofCharacter χ - counit α R

@[simp]
theorem augmentationPart_eval_empty
    {α : Type u} {R : Type v} [CommRing R]
    (χ : LForestAlgebra.Character α R) :
    evalForest (augmentationPart χ) LRootedForest.empty = 0 := by
  simp [augmentationPart, evalForest, ofCharacter, counit]

theorem agreeUpToOrder_augmentationPart
    {α : Type u} {R : Type v} [CommRing R]
    {χ ψ : LForestAlgebra.Character α R} {n : Nat}
    (h : ∀ φ, LRootedForest.order φ ≤ n → χ.evalForest φ = ψ.evalForest φ) :
    AgreeUpToOrder (augmentationPart χ) (augmentationPart ψ) n := by
  intro φ hφ
  simp [augmentationPart, evalForest, ofCharacter, counit]
  simpa [LForestAlgebra.Character.evalForest] using h φ hφ

theorem augmentationPart_comapMapLabels {β : Type w} (f : α → β)
    {R : Type v} [CommRing R] (χ : LForestAlgebra.Character β R) :
    augmentationPart (LForestAlgebra.Character.comapMapLabels f χ) =
      comapMapLabels f (augmentationPart χ) := by
  rw [augmentationPart]
  change
    ofCharacter (LForestAlgebra.Character.comapMapLabels f χ) - counit α R =
      comapMapLabels f (ofCharacter χ - counit β R)
  rw [← comapMapLabels_ofCharacter f χ, ← comapMapLabels_counit f]
  ext x
  rfl

theorem augmentationPart_comapEraseLabels
    {R : Type v} [CommRing R] (χ : ForestAlgebra.Character R) :
    augmentationPart (LForestAlgebra.Character.comapEraseLabels (α := α) χ) =
      comapEraseLabels (α := α)
        (ForestAlgebra.LinearFunctional.augmentationPart χ) := by
  rw [augmentationPart, ForestAlgebra.LinearFunctional.augmentationPart]
  rw [← comapEraseLabels_ofCharacter χ, ← comapEraseLabels_counit]
  ext x
  rfl

theorem augmentationPart_comapConstLabel
    (a : α) {R : Type v} [CommRing R] (χ : LForestAlgebra.Character α R) :
    ForestAlgebra.LinearFunctional.augmentationPart
        (LForestAlgebra.Character.comapConstLabel a χ) =
      comapConstLabel a (augmentationPart χ) := by
  rw [ForestAlgebra.LinearFunctional.augmentationPart, augmentationPart]
  rw [← comapConstLabel_ofCharacter a χ, ← comapConstLabel_counit a]
  ext x
  rfl

/-- The truncated convolution logarithm of a labelled forest character. -/
def logCharacterTruncated {α : Type u} {R : Type v} [Field R]
    (χ : LForestAlgebra.Character α R) (n : Nat) :
    LForestAlgebra.LinearFunctional α R :=
  ((List.range n).map fun i =>
    let k : Nat := i + 1
    (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) •
      convolutionPower (augmentationPart χ) k).sum

@[simp]
theorem logCharacterTruncated_zero
    {α : Type u} {R : Type v} [Field R]
    (χ : LForestAlgebra.Character α R) :
    logCharacterTruncated χ 0 = 0 := by
  simp [logCharacterTruncated]

theorem logCharacterTruncated_evalForest
    {α : Type u} {R : Type v} [Field R]
    (χ : LForestAlgebra.Character α R) (n : Nat) (φ : LRootedForest α) :
    evalForest (logCharacterTruncated χ n) φ =
      ((List.range n).map fun i =>
        let k : Nat := i + 1
        (((-1 : R) ^ (k + 1)) * (k : R)⁻¹) *
          evalForest (convolutionPower (augmentationPart χ) k) φ).sum := by
  unfold logCharacterTruncated
  rw [evalForest_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  simp [evalForest]

theorem agreeUpToOrder_logCharacterTruncated
    {α : Type u} {R : Type v} [Field R]
    {χ ψ : LForestAlgebra.Character α R} {m n : Nat}
    (h : ∀ φ, LRootedForest.order φ ≤ n → χ.evalForest φ = ψ.evalForest φ) :
    AgreeUpToOrder (logCharacterTruncated χ m) (logCharacterTruncated ψ m) n := by
  intro φ hφ
  rw [logCharacterTruncated_evalForest, logCharacterTruncated_evalForest]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  dsimp
  have hp :
      evalForest (convolution (augmentationPart χ)
        (convolutionPower (augmentationPart χ) i)) φ =
        evalForest (convolution (augmentationPart ψ)
          (convolutionPower (augmentationPart ψ) i)) φ := by
    simpa [convolutionPower] using
      (agreeUpToOrder_augmentationPart h).convolutionPower (i + 1) φ hφ
  rw [hp]

theorem logCharacterTruncated_comapMapLabels {β : Type w} (f : α → β)
    {R : Type v} [Field R] (χ : LForestAlgebra.Character β R) (n : Nat) :
    logCharacterTruncated (LForestAlgebra.Character.comapMapLabels f χ) n =
      comapMapLabels f (logCharacterTruncated χ n) := by
  unfold logCharacterTruncated
  rw [comapMapLabels_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  dsimp
  rw [augmentationPart_comapMapLabels, convolutionPower_comapMapLabels,
    convolution_comapMapLabels, comapMapLabels_smul]

theorem logCharacterTruncated_comapEraseLabels
    {R : Type v} [Field R] (χ : ForestAlgebra.Character R) (n : Nat) :
    logCharacterTruncated (LForestAlgebra.Character.comapEraseLabels (α := α) χ) n =
      comapEraseLabels (α := α)
        (ForestAlgebra.LinearFunctional.logCharacterTruncated χ n) := by
  unfold logCharacterTruncated ForestAlgebra.LinearFunctional.logCharacterTruncated
  rw [comapEraseLabels_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  dsimp
  rw [augmentationPart_comapEraseLabels, convolutionPower_comapEraseLabels,
    convolution_comapEraseLabels, comapEraseLabels_smul]

theorem logCharacterTruncated_comapConstLabel
    (a : α) {R : Type v} [Field R]
    (χ : LForestAlgebra.Character α R) (n : Nat) :
    ForestAlgebra.LinearFunctional.logCharacterTruncated
        (LForestAlgebra.Character.comapConstLabel a χ) n =
      comapConstLabel a (logCharacterTruncated χ n) := by
  unfold ForestAlgebra.LinearFunctional.logCharacterTruncated logCharacterTruncated
  rw [comapConstLabel_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _hi
  dsimp
  rw [augmentationPart_comapConstLabel, convolutionPower_comapConstLabel,
    convolution_comapConstLabel, comapConstLabel_smul]

theorem convolution_compAntipode_ofCharacter_left
    {α : Type u} {R : Type v} [CommRing R]
    (χ : LForestAlgebra.Character α R) :
    convolution (compAntipode (ofCharacter χ)) (ofCharacter χ) =
      counit α R := by
  apply LinearMap.ext
  intro x
  change
    LForestTensorAlgebra.evalByLinearMaps
        ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
          (LForestAlgebra.antipode (R := R)))
        (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap
        (LForestAlgebra.coproduct α R x) =
      LForestAlgebra.counit α R x
  rw [LForestTensorAlgebra.evalByLinearMaps_compAntipode_ofCharacter]
  exact LForestAlgebra.Character.eval_antipodeLeft_coproduct χ x

theorem convolution_compRightAntipode_ofCharacter_right
    {α : Type u} {R : Type v} [CommRing R]
    (χ : LForestAlgebra.Character α R) :
    convolution (ofCharacter χ) (compRightAntipode (ofCharacter χ)) =
      counit α R := by
  apply LinearMap.ext
  intro x
  change
    LForestTensorAlgebra.evalByLinearMaps
        (χ : LForestAlgebra α R →ₐ[R] R).toLinearMap
        ((χ : LForestAlgebra α R →ₐ[R] R).toLinearMap.comp
          (LForestAlgebra.rightAntipode (R := R)))
        (LForestAlgebra.coproduct α R x) =
      LForestAlgebra.counit α R x
  rw [LForestTensorAlgebra.evalByLinearMaps_compRightAntipode_ofCharacter]
  exact LForestAlgebra.Character.eval_antipodeRight_coproduct χ x

theorem compAntipode_ofCharacter_eq_compRightAntipode
    {α : Type u} {R : Type v} [CommRing R]
    (χ : LForestAlgebra.Character α R) :
    compAntipode (ofCharacter χ) = compRightAntipode (ofCharacter χ) := by
  calc
    compAntipode (ofCharacter χ) =
        convolution (compAntipode (ofCharacter χ)) (counit α R) := by
          rw [convolution_counit_right]
    _ = convolution (compAntipode (ofCharacter χ))
        (convolution (ofCharacter χ) (compRightAntipode (ofCharacter χ))) := by
          rw [convolution_compRightAntipode_ofCharacter_right χ]
    _ = convolution (convolution (compAntipode (ofCharacter χ)) (ofCharacter χ))
        (compRightAntipode (ofCharacter χ)) := by
          rw [convolution_assoc]
    _ = convolution (counit α R) (compRightAntipode (ofCharacter χ)) := by
          rw [convolution_compAntipode_ofCharacter_left χ]
    _ = compRightAntipode (ofCharacter χ) := by
          rw [convolution_counit_left]

end

end LinearFunctional

namespace Character

noncomputable section

variable {α : Type u} {R : Type v} [CommRing R]

/-- The antipode-composed linear functional that gives the convolution inverse of a character. -/
def inverseLinearFunctional (χ : LForestAlgebra.Character α R) :
    LForestAlgebra.LinearFunctional α R :=
  LForestAlgebra.LinearFunctional.compAntipode
    (LForestAlgebra.LinearFunctional.ofCharacter χ)

theorem convolution_inverseLinearFunctional_left (χ : LForestAlgebra.Character α R) :
    LForestAlgebra.LinearFunctional.convolution (inverseLinearFunctional χ)
        (LForestAlgebra.LinearFunctional.ofCharacter χ) =
      LForestAlgebra.LinearFunctional.counit α R := by
  exact LForestAlgebra.LinearFunctional.convolution_compAntipode_ofCharacter_left χ

theorem convolution_inverseLinearFunctional_right (χ : LForestAlgebra.Character α R) :
    LForestAlgebra.LinearFunctional.convolution
        (LForestAlgebra.LinearFunctional.ofCharacter χ) (inverseLinearFunctional χ) =
      LForestAlgebra.LinearFunctional.counit α R := by
  rw [inverseLinearFunctional,
    LForestAlgebra.LinearFunctional.compAntipode_ofCharacter_eq_compRightAntipode χ]
  exact LForestAlgebra.LinearFunctional.convolution_compRightAntipode_ofCharacter_right χ

end

end Character

end LForestAlgebra

end HopfAlgebras
