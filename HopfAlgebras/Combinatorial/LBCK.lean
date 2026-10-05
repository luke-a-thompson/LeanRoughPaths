/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Combinatorial.Basic
import HopfAlgebras.Hopf.LabelledCharacterConvolution

/-!
# The labelled Butcher–Connes–Kreimer bialgebra as a combinatorial bialgebra

The labelled BCK Hopf algebra of decorated non-planar rooted forests,
packaged as a `CombBialg`, mirroring `HopfAlgebras.Combinatorial.BCK`:
monomial forest-union product, admissible-cut coproduct
`LRootedForest.coproductTerms`. Characters of the labelled forest
algebra correspond to combinatorial characters via the
`AddMonoidAlgebra.lift` bridge `lbckCharacter` /
`evalForest_lbckIsCharacter`.
-/

namespace HopfAlgebras

universe u v

namespace LBCK

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

/-- The labelled counit coefficient as a Boolean if-then-else. -/
theorem counitCoeff_eq_boolIte {α : Type u} {R : Type v} [CommSemiring R]
    (φ : LRootedForest α) :
    LForestAlgebra.counitCoeff (R := R) φ =
      (if (decide (Multiset.card φ = 0) : Bool) then (1 : R) else 0) := by
  by_cases h : φ = 0
  · subst h
    rw [LForestAlgebra.counitCoeff_zero,
      show (decide (Multiset.card (0 : LRootedForest α) = 0)) = true from
        by simp]
    exact (if_pos rfl).symm
  · rw [LForestAlgebra.counitCoeff_ne_zero h,
      show (decide (Multiset.card φ = 0)) = false from by
        simp [Multiset.card_eq_zero, h]]
    exact (if_neg Bool.false_ne_true).symm

/-- Pair a labelled forest-algebra element against an arbitrary
coefficient function, linearly in the element. -/
private noncomputable def pairWith {α : Type u} {R : Type v}
    [CommSemiring R] (f : LRootedForest α → R) :
    LForestAlgebra α R →ₗ[R] R :=
  (Finsupp.linearCombination R f).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

private theorem pairWith_ofForest {α : Type u} {R : Type v}
    [CommSemiring R] (f : LRootedForest α → R) (ξ : LRootedForest α) :
    pairWith f (LForestAlgebra.ofForest (R := R) ξ) = f ξ := by
  change Finsupp.linearCombination R f (Finsupp.single ξ (1 : R)) = f ξ
  rw [Finsupp.linearCombination_single, one_smul]

end LBCK

/-- **The labelled BCK bialgebra of decorated rooted forests** as a
combinatorial bialgebra: monomial forest-union product and
admissible-cut coproduct. -/
noncomputable def lbckBialg (α : Type u) :
    CombBialg.{u, v} (LRootedForest α) where
  mul x y := [x + y]
  one := 0
  coprod := LRootedForest.coproductTerms
  isOne x := decide (Multiset.card x = 0)
  isOne_iff := fun x => by simp [Multiset.card_eq_zero]
  mul_one_expand x := by rw [add_zero]
  one_mul_expand x := by rw [zero_add]
  coprod_one := by
    show LRootedForest.coproductTerms 0 = [(0, 0)]
    rw [LRootedForest.coproductTerms]
    have hout : (Quotient.out (0 : LRootedForest α)) =
        ([] : List (LRootedTree α)) := by
      have h : ((Quotient.out (0 : LRootedForest α) :
          List (LRootedTree α)) : Multiset (LRootedTree α)) = 0 :=
        Quotient.out_eq _
      exact (Multiset.coe_eq_zero _).mp h
    rw [hout]
    rfl
  coassoc := by
    intro R _ f g h x
    have hperm : (LForestTripleTensorAlgebra.coproductLeftTerms
        (LRootedForest.coproductTerms x)).Perm
        (LForestTripleTensorAlgebra.coproductRightTerms
          (LRootedForest.coproductTerms x)) :=
      LForestTripleTensorAlgebra.coproductTerms_lrootedForest_left_right_perm_of_coproductTerms_perm
        LForestTripleTensorAlgebra.coproductTerms_left_right_perm x
    have hpair := (hperm.map fun r => f r.1 * g r.2.1 * h r.2.2).sum_eq
    have hL : ((LForestTripleTensorAlgebra.coproductLeftTerms
        (LRootedForest.coproductTerms x)).map
          fun r => f r.1 * g r.2.1 * h r.2.2).sum =
        ((LRootedForest.coproductTerms x).map fun p =>
          (((LRootedForest.coproductTerms p.1).map fun l =>
            ((l.1, l.2, p.2) :
              LRootedForest α × LRootedForest α × LRootedForest α)).map
                fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum :=
      LBCK.sum_flatMap _ _ _
    have hR : ((LForestTripleTensorAlgebra.coproductRightTerms
        (LRootedForest.coproductTerms x)).map
          fun r => f r.1 * g r.2.1 * h r.2.2).sum =
        ((LRootedForest.coproductTerms x).map fun p =>
          (((LRootedForest.coproductTerms p.2).map fun q =>
            ((p.1, q.1, q.2) :
              LRootedForest α × LRootedForest α × LRootedForest α)).map
                fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum :=
      LBCK.sum_flatMap _ _ _
    have hA : ((LRootedForest.coproductTerms x).map fun p =>
        ((LRootedForest.coproductTerms p.1).map
          fun q => f q.1 * g q.2).sum * h p.2).sum =
        ((LRootedForest.coproductTerms x).map fun p =>
          (((LRootedForest.coproductTerms p.1).map fun l =>
            ((l.1, l.2, p.2) :
              LRootedForest α × LRootedForest α × LRootedForest α)).map
                fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum := by
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      rw [← List.sum_map_mul_right, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun l _ => rfl)
    have hB : ((LRootedForest.coproductTerms x).map fun p =>
        (((LRootedForest.coproductTerms p.2).map fun q =>
          ((p.1, q.1, q.2) :
            LRootedForest α × LRootedForest α × LRootedForest α)).map
              fun r => f r.1 * g r.2.1 * h r.2.2).sum).sum =
        ((LRootedForest.coproductTerms x).map fun p =>
          f p.1 * ((LRootedForest.coproductTerms p.2).map
            fun q => g q.1 * h q.2).sum).sum := by
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      rw [← List.sum_map_mul_left, List.map_map]
      exact congrArg List.sum
        (List.map_congr_left fun q _ => mul_assoc _ _ _)
    exact hA.trans ((hL.symm.trans hpair).trans (hR.trans hB))
  counit_left := by
    intro R _ f x
    have hseries : ((LRootedForest.coproductTerms x).map fun term =>
        LForestAlgebra.counitCoeff (R := R) term.1 •
          LForestAlgebra.ofForest (R := R) term.2).sum =
        LForestAlgebra.ofForest (R := R) x := by
      rw [← LForestTensorAlgebra.counitLeft_sumTerms,
        ← LRootedForest.coproduct_eq_sumTerms_coproductTerms,
        LRootedForest.counitLeft_coproduct]
    have hpair := congrArg (LBCK.pairWith (R := R) f) hseries
    rw [map_list_sum, List.map_map, LBCK.pairWith_ofForest] at hpair
    refine Eq.trans ?_ hpair
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    show (if (decide (Multiset.card p.1 = 0) : Bool) then (1 : R)
        else 0) * f p.2 =
      LBCK.pairWith f (LForestAlgebra.counitCoeff (R := R) p.1 •
        LForestAlgebra.ofForest (R := R) p.2)
    rw [map_smul, smul_eq_mul, LBCK.pairWith_ofForest,
      LBCK.counitCoeff_eq_boolIte]
  counit_right := by
    intro R _ f x
    have hseries : ((LRootedForest.coproductTerms x).map fun term =>
        LForestAlgebra.counitCoeff (R := R) term.2 •
          LForestAlgebra.ofForest (R := R) term.1).sum =
        LForestAlgebra.ofForest (R := R) x := by
      rw [← LForestTensorAlgebra.counitRight_sumTerms,
        ← LRootedForest.coproduct_eq_sumTerms_coproductTerms,
        LRootedForest.counitRight_coproduct]
    have hpair := congrArg (LBCK.pairWith (R := R) f) hseries
    rw [map_list_sum, List.map_map, LBCK.pairWith_ofForest] at hpair
    refine Eq.trans ?_ hpair
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    show f p.1 * (if (decide (Multiset.card p.2 = 0) : Bool) then (1 : R)
        else 0) =
      LBCK.pairWith f (LForestAlgebra.counitCoeff (R := R) p.2 •
        LForestAlgebra.ofForest (R := R) p.1)
    rw [map_smul, smul_eq_mul, LBCK.pairWith_ofForest,
      LBCK.counitCoeff_eq_boolIte, mul_comm]
  mul_count_one := by
    intro R _ x y
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    by_cases hx : x = 0
    · subst hx
      rw [zero_add,
        show (decide (Multiset.card (0 : LRootedForest α) = 0)) =
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
      ((LRootedForest.coproductTerms_add_perm x y).map
        fun p => φ p.1 * ψ p.2).sum_eq,
      show ((PLTree.multiplyCoproductTerms (LRootedForest.coproductTerms x)
          (LRootedForest.coproductTerms y)).map
            fun p => φ p.1 * ψ p.2).sum =
        ((LRootedForest.coproductTerms x).map fun p =>
          (((LRootedForest.coproductTerms y).map fun q =>
            ((p.1 + q.1, p.2 + q.2) :
              LRootedForest α × LRootedForest α)).map
                fun r => φ r.1 * ψ r.2).sum).sum from
        LBCK.sum_flatMap _ _ _]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    show φ (p.1 + q.1) * ψ (p.2 + q.2) =
      (([(p.1 + q.1 : LRootedForest α)]).map φ).sum *
        (([(p.2 + q.2 : LRootedForest α)]).map ψ).sum
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]

/-! ### Characters of the labelled forest algebra vs combinatorial
characters -/

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- The coefficient system of a labelled forest-algebra character is a
character of the labelled BCK combinatorial bialgebra. -/
theorem evalForest_lbckIsCharacter (χ : LForestAlgebra.Character α R) :
    (lbckBialg α).IsCharacter χ.evalForest := by
  constructor
  · exact LForestAlgebra.Character.evalForest_zero χ
  · intro x y
    show χ.evalForest x * χ.evalForest y =
      (([x + y] : List (LRootedForest α)).map χ.evalForest).sum
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, LForestAlgebra.Character.evalForest_add]

/-- **Labelled character convolution is the abstract convolution**. -/
theorem convolution_evalForest_lconv (χ ψ : LForestAlgebra.Character α R)
    (φ : LRootedForest α) :
    (LForestAlgebra.Character.convolution χ ψ).evalForest φ =
      CombBialg.Character.conv (H := lbckBialg α)
        χ.evalForest ψ.evalForest φ := by
  rw [LForestAlgebra.Character.convolution_evalForest]
  show LForestTensorAlgebra.evalByCharacters χ ψ
    (LRootedForest.coproduct (R := R) φ) = _
  rw [LRootedForest.coproduct_eq_sumTerms_coproductTerms,
    LForestTensorAlgebra.evalByCharacters_sumTerms]
  rfl

private def lbckMonoidHom (f : LRootedForest α → R)
    (hf : (lbckBialg α).IsCharacter f) :
    Multiplicative (LRootedForest α) →* R where
  toFun φ := f (Multiplicative.toAdd φ)
  map_one' := hf.1
  map_mul' φ ψ := by
    have h : f (Multiplicative.toAdd φ) * f (Multiplicative.toAdd ψ) =
        f (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) + 0 :=
      hf.2 (Multiplicative.toAdd φ) (Multiplicative.toAdd ψ)
    rw [add_zero] at h
    exact h.symm

/-- Lift a character of the labelled BCK combinatorial bialgebra to an
algebra character of the labelled forest algebra. -/
noncomputable def lbckCharacter (f : LRootedForest α → R)
    (hf : (lbckBialg α).IsCharacter f) : LForestAlgebra.Character α R :=
  (AddMonoidAlgebra.lift R R (LRootedForest α)) (lbckMonoidHom f hf)

@[simp]
theorem evalForest_lbckCharacter (f : LRootedForest α → R)
    (hf : (lbckBialg α).IsCharacter f) (φ : LRootedForest α) :
    (lbckCharacter f hf).evalForest φ = f φ := by
  change (AddMonoidAlgebra.lift R R (LRootedForest α))
    (lbckMonoidHom f hf) (AddMonoidAlgebra.single φ (1 : R)) = f φ
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

end HopfAlgebras
