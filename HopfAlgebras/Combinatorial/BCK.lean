/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Combinatorial.Basic
import HopfAlgebras.Hopf.CharacterConvolution

/-!
# The Butcher–Connes–Kreimer bialgebra as a combinatorial bialgebra

The BCK Hopf algebra of non-planar rooted forests, packaged as a
`CombBialg`: the product is the (monomial) forest union, the coproduct
the admissible-cut expansion `RootedForest.coproductTerms` from
`HopfAlgebras`. Its characters — the multiplicative functionals on
forests, i.e. the coefficient systems of branched rough paths and
B-series — thereby inherit the abstract convolution monoid of
`HopfAlgebra.Basic`.

All axioms are discharged from the cut-combinatorics keystones already
in `HopfAlgebras`: `coproductTerms_add_perm` (bialgebra compatibility),
`nestedCoproductTerms_left_right_perm` (coassociativity) and the
series-level counit laws `counitLeft_coproduct`/`counitRight_coproduct`,
paired against arbitrary coefficient functions via
`Finsupp.linearCombination`.
-/

namespace HopfAlgebras

open HopfAlgebras

universe v

namespace BCK

/-- Sums along permuted lists agree. -/
private theorem sum_map_perm {γ : Type*} {R : Type*} [AddCommMonoid R]
    {l₁ l₂ : List γ} (h : l₁.Perm l₂) (g : γ → R) :
    (l₁.map g).sum = (l₂.map g).sum :=
  (h.map g).sum_eq

/-- Peel a sum over a `flatMap` into iterated sums. -/
private theorem sum_flatMap {β γ : Type*} {R : Type*}
    [AddCommMonoid R] (l : List β) (f : β → List γ) (g : γ → R) :
    ((l.flatMap f).map g).sum =
      (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
        List.map_cons, List.sum_cons]

/-- The counit coefficient as a Boolean if-then-else. -/
theorem counitCoeff_eq_boolIte {R : Type v} [CommSemiring R]
    (φ : RootedForest) :
    ForestAlgebra.counitCoeff (R := R) φ =
      (if (decide (Multiset.card φ = 0) : Bool) then (1 : R) else 0) := by
  by_cases h : φ = 0
  · subst h
    rw [ForestAlgebra.counitCoeff_zero,
      show (decide (Multiset.card (0 : RootedForest) = 0)) = true from
        by simp]
    exact (if_pos rfl).symm
  · rw [ForestAlgebra.counitCoeff_ne_zero h,
      show (decide (Multiset.card φ = 0)) = false from by
        simp [Multiset.card_eq_zero, h]]
    exact (if_neg Bool.false_ne_true).symm

/-- Pair a forest-algebra element against an arbitrary coefficient
function, linearly in the element. -/
private noncomputable def pairWith {R : Type v} [CommSemiring R]
    (f : RootedForest → R) : ForestAlgebra R →ₗ[R] R :=
  (Finsupp.linearCombination R f).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

private theorem pairWith_ofForest {R : Type v} [CommSemiring R]
    (f : RootedForest → R) (ξ : RootedForest) :
    pairWith f (ForestAlgebra.ofForest (R := R) ξ) = f ξ := by
  change Finsupp.linearCombination R f (Finsupp.single ξ (1 : R)) = f ξ
  rw [Finsupp.linearCombination_single, one_smul]

end BCK

/-- **The BCK bialgebra of rooted forests** as a combinatorial
bialgebra: monomial forest-union product and admissible-cut coproduct. -/
noncomputable def bckBialg : CombBialg.{0, v} RootedForest where
  mul x y := [x + y]
  one := 0
  coprod := RootedForest.coproductTerms
  isOne x := decide (Multiset.card x = 0)
  isOne_iff := fun x => by simp [Multiset.card_eq_zero]
  mul_one_expand x := by rw [add_zero]
  one_mul_expand x := by rw [zero_add]
  coprod_one := by
    show RootedForest.coproductTerms 0 = [(0, 0)]
    rw [RootedForest.coproductTerms]
    have hout : (Quotient.out (0 : RootedForest)) =
        ([] : List RootedTree) := by
      have h : ((Quotient.out (0 : RootedForest) : List RootedTree) :
          Multiset RootedTree) = 0 := Quotient.out_eq _
      exact (Multiset.coe_eq_zero _).mp h
    rw [hout]
    rfl
  coassoc := by
    intro R _ f g h x
    -- the triple-terms permutation, from the PTree-level keystone
    have hperm : (ForestTripleTensorAlgebra.coproductLeftTerms
        (RootedForest.coproductTerms x)).Perm
        (ForestTripleTensorAlgebra.coproductRightTerms
          (RootedForest.coproductTerms x)) :=
      ForestTripleTensorAlgebra.coproductTerms_rootedForest_left_right_perm_of_nestedCoproductTerms_perm
        ForestTripleTensorAlgebra.nestedCoproductTerms_left_right_perm x
    have hpair := (hperm.map fun r => f r.1 * g r.2.1 * h r.2.2).sum_eq
    -- peel both triple sums into iterated sums
    have hL : ((ForestTripleTensorAlgebra.coproductLeftTerms
        (RootedForest.coproductTerms x)).map
          fun r => f r.1 * g r.2.1 * h r.2.2).sum =
        ((RootedForest.coproductTerms x).map fun p =>
          (((RootedForest.coproductTerms p.1).map fun l =>
            ((l.1, l.2, p.2) :
              RootedForest × RootedForest × RootedForest)).map
                fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum :=
      BCK.sum_flatMap _ _ _
    have hR : ((ForestTripleTensorAlgebra.coproductRightTerms
        (RootedForest.coproductTerms x)).map
          fun r => f r.1 * g r.2.1 * h r.2.2).sum =
        ((RootedForest.coproductTerms x).map fun p =>
          (((RootedForest.coproductTerms p.2).map fun q =>
            ((p.1, q.1, q.2) :
              RootedForest × RootedForest × RootedForest)).map
                fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum :=
      BCK.sum_flatMap _ _ _
    have hA : ((RootedForest.coproductTerms x).map fun p =>
        ((RootedForest.coproductTerms p.1).map
          fun q => f q.1 * g q.2).sum * h p.2).sum =
        ((RootedForest.coproductTerms x).map fun p =>
          (((RootedForest.coproductTerms p.1).map fun l =>
            ((l.1, l.2, p.2) :
              RootedForest × RootedForest × RootedForest)).map
                fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum := by
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      rw [← List.sum_map_mul_right, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun l _ => rfl)
    have hB : ((RootedForest.coproductTerms x).map fun p =>
        (((RootedForest.coproductTerms p.2).map fun q =>
          ((p.1, q.1, q.2) :
            RootedForest × RootedForest × RootedForest)).map
              fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum =
        ((RootedForest.coproductTerms x).map fun p =>
          f p.1 * ((RootedForest.coproductTerms p.2).map
            fun q => g q.1 * h q.2).sum).sum := by
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      rw [← List.sum_map_mul_left, List.map_map]
      exact congrArg List.sum
        (List.map_congr_left fun q _ => mul_assoc _ _ _)
    exact hA.trans ((hL.symm.trans hpair).trans (hR.trans hB))
  counit_left := by
    intro R _ f x
    -- the series-level counit law, restated over the term list
    have hseries : ((RootedForest.coproductTerms x).map fun term =>
        ForestAlgebra.counitCoeff (R := R) term.1 •
          ForestAlgebra.ofForest (R := R) term.2).sum =
        ForestAlgebra.ofForest (R := R) x := by
      rw [← ForestTensorAlgebra.counitLeft_sumTerms,
        ← RootedForest.coproduct_eq_sumTerms_coproductTerms,
        RootedForest.counitLeft_coproduct]
    -- pair against `f`
    have hpair := congrArg (BCK.pairWith (R := R) f) hseries
    rw [map_list_sum, List.map_map, BCK.pairWith_ofForest] at hpair
    refine Eq.trans ?_ hpair
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    show (if (decide (Multiset.card p.1 = 0) : Bool) then (1 : R)
        else 0) * f p.2 =
      BCK.pairWith f (ForestAlgebra.counitCoeff (R := R) p.1 •
        ForestAlgebra.ofForest (R := R) p.2)
    rw [map_smul, smul_eq_mul, BCK.pairWith_ofForest,
      BCK.counitCoeff_eq_boolIte]
  counit_right := by
    intro R _ f x
    have hseries : ((RootedForest.coproductTerms x).map fun term =>
        ForestAlgebra.counitCoeff (R := R) term.2 •
          ForestAlgebra.ofForest (R := R) term.1).sum =
        ForestAlgebra.ofForest (R := R) x := by
      rw [← ForestTensorAlgebra.counitRight_sumTerms,
        ← RootedForest.coproduct_eq_sumTerms_coproductTerms,
        RootedForest.counitRight_coproduct]
    have hpair := congrArg (BCK.pairWith (R := R) f) hseries
    rw [map_list_sum, List.map_map, BCK.pairWith_ofForest] at hpair
    refine Eq.trans ?_ hpair
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    show f p.1 * (if (decide (Multiset.card p.2 = 0) : Bool) then (1 : R)
        else 0) =
      BCK.pairWith f (ForestAlgebra.counitCoeff (R := R) p.2 •
        ForestAlgebra.ofForest (R := R) p.1)
    rw [map_smul, smul_eq_mul, BCK.pairWith_ofForest,
      BCK.counitCoeff_eq_boolIte, mul_comm]
  mul_count_one := by
    intro R _ x y
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    by_cases hx : x = 0
    · subst hx
      rw [zero_add, show (decide (Multiset.card (0 : RootedForest) = 0)) =
        true from rfl]
      show (if decide (Multiset.card y = 0) then (1 : R) else 0) =
        (1 : R) * (if decide (Multiset.card y = 0) then (1 : R) else 0)
      rw [one_mul]
    · have hxb : (decide (Multiset.card x = 0)) = false := by
        simp [Multiset.card_eq_zero, hx]
      have hxyb : (decide (Multiset.card (x + y) = 0)) = false := by
        simp only [decide_eq_false_iff_not, Multiset.card_eq_zero]
        exact fun h => hx (add_eq_zero.mp h).1
      rw [hxb, hxyb]
      show (0 : R) = 0 * (if decide (Multiset.card y = 0) then (1 : R)
        else 0)
      rw [zero_mul]
  bialg := by
    intro R _ φ ψ x y
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero,
      ((RootedForest.coproductTerms_add_perm x y).map
        fun p => φ p.1 * ψ p.2).sum_eq,
      show ((PTree.multiplyCoproductTerms (RootedForest.coproductTerms x)
          (RootedForest.coproductTerms y)).map
            fun p => φ p.1 * ψ p.2).sum =
        ((RootedForest.coproductTerms x).map fun p =>
          (((RootedForest.coproductTerms y).map fun q =>
            ((p.1 + q.1, p.2 + q.2) :
              RootedForest × RootedForest)).map
                fun r => φ r.1 * ψ r.2).sum).sum from
        BCK.sum_flatMap _ _ _]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    show φ (p.1 + q.1) * ψ (p.2 + q.2) =
      (([(p.1 + q.1 : RootedForest)]).map φ).sum *
        (([(p.2 + q.2 : RootedForest)]).map ψ).sum
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]

/-! ### Characters of the forest algebra vs combinatorial characters -/

variable {R : Type v} [CommSemiring R]

/-- The coefficient system of a forest-algebra character is a character
of the BCK combinatorial bialgebra. -/
theorem evalForest_isCharacter (χ : ForestAlgebra.Character R) :
    bckBialg.IsCharacter χ.evalForest := by
  constructor
  · exact ForestAlgebra.Character.evalForest_zero χ
  · intro x y
    show χ.evalForest x * χ.evalForest y =
      (([x + y] : List RootedForest).map χ.evalForest).sum
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, ForestAlgebra.Character.evalForest_add]

/-- **Character convolution is the abstract BCK convolution**. -/
theorem convolution_evalForest_conv (χ ψ : ForestAlgebra.Character R)
    (φ : RootedForest) :
    (ForestAlgebra.Character.convolution χ ψ).evalForest φ =
      CombBialg.Character.conv (H := bckBialg)
        χ.evalForest ψ.evalForest φ := by
  rw [ForestAlgebra.Character.convolution_evalForest]
  show ForestTensorAlgebra.evalByCharacters χ ψ
    (RootedForest.coproduct (R := R) φ) = _
  rw [RootedForest.coproduct_eq_sumTerms_coproductTerms,
    ForestTensorAlgebra.evalByCharacters_sumTerms]
  rfl

private def bckMonoidHom (f : RootedForest → R)
    (hf : bckBialg.IsCharacter f) :
    Multiplicative RootedForest →* R where
  toFun φ := f (Multiplicative.toAdd φ)
  map_one' := hf.1
  map_mul' φ ψ := by
    have h : f (Multiplicative.toAdd φ) * f (Multiplicative.toAdd ψ) =
        f (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) + 0 :=
      hf.2 (Multiplicative.toAdd φ) (Multiplicative.toAdd ψ)
    rw [add_zero] at h
    exact h.symm

/-- Lift a character of the combinatorial BCK bialgebra to an algebra
character of the forest algebra. -/
noncomputable def bckCharacter (f : RootedForest → R)
    (hf : bckBialg.IsCharacter f) : ForestAlgebra.Character R :=
  (AddMonoidAlgebra.lift R R RootedForest) (bckMonoidHom f hf)

@[simp]
theorem evalForest_bckCharacter (f : RootedForest → R)
    (hf : bckBialg.IsCharacter f) (φ : RootedForest) :
    (bckCharacter f hf).evalForest φ = f φ := by
  change (AddMonoidAlgebra.lift R R RootedForest) (bckMonoidHom f hf)
    (AddMonoidAlgebra.single φ (1 : R)) = f φ
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

end HopfAlgebras
