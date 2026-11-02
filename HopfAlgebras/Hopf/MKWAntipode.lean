/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.MKWCoproduct
import HopfAlgebras.Util.List
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The Munthe-Kaas-Wright Antipode

This file defines the antipode of the Munthe-Kaas-Wright Hopf algebra of
ordered forests, following the recursion of Munthe-Kaas & Wright,
*On the Hopf algebraic structure of Lie group integrators*
(Found. Comput. Math. 8, 2008; arXiv:math/0603023), Theorem 2:

  `S_N(𝟙) = 𝟙`,
  `S_N(ω τ) = -μ_N((S_N ⊗ I)(Δ_N(ω) ⊔·(I ⊗ B⁺)Δ_N(B⁻(τ))))`,

where `μ_N` is the shuffle product of ordered forests. The argument of
`S_N ⊗ I` consists of all MKW coproduct terms except the full cut
`ωτ ⊗ 𝟙`, and every such term prunes strictly fewer vertices, so the
recursion is well-founded by forest order.

## Main definitions

* `PlanarForestAlgebra.shuffleOf` - the shuffle product of two ordered forests
* `PlanarForestAlgebra.shuffleRight` - shuffle a general element with a forest
* `PlanarForest.mkwAntipode` - the MKW antipode
* `PlanarForest.sum_shuffleRight_mkwAntipode_mkwTerms` - the left antipode
  identity `μ_N(S_N ⊗ I)Δ_N = u_N ∘ e_N`

The antipode is verified on forests of order at most two.
-/

namespace HopfAlgebras

open HopfAlgebras

universe u

namespace PlanarForestAlgebra

noncomputable section

variable {R : Type u}

/-- The shuffle product of two ordered forests in the ordered forest algebra.
This is the product `μ_N` of the MKW Hopf algebra. -/
def shuffleOf [Semiring R] (ts us : PlanarForest) : PlanarForestAlgebra R :=
  ((Word.shuffle ts us).map fun vs => ofForest (R := R) vs).sum

@[simp]
theorem shuffleOf_nil_left [Semiring R] (us : PlanarForest) :
    shuffleOf (R := R) [] us = ofForest us := by
  simp [shuffleOf]

@[simp]
theorem shuffleOf_nil_right [Semiring R] (ts : PlanarForest) :
    shuffleOf (R := R) ts [] = ofForest ts := by
  simp [shuffleOf]

theorem shuffleOf_singleton_singleton [Semiring R] (t u : PTree) :
    shuffleOf (R := R) [t] [u] = ofForest [t, u] + ofForest [u, t] := by
  rw [shuffleOf]
  simp only [Word.shuffle_cons_cons, Word.shuffle_nil_left, Word.shuffle_nil_right,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.sum_cons, List.sum_nil, add_zero]

/-- Shuffling with a fixed forest on the right, extended linearly in the
left argument. The fixed forest comes first so `shuffleRight us` is a linear map. -/
def shuffleRight [Semiring R] (us : PlanarForest) :
    PlanarForestAlgebra R →ₗ[R] PlanarForestAlgebra R :=
  (Finsupp.linearCombination R (fun ts => shuffleOf (R := R) ts us)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem shuffleRight_single_left [Semiring R] (ts : PlanarForest) (a : R)
    (us : PlanarForest) :
    shuffleRight us (MonoidAlgebra.single ts a) = a • shuffleOf ts us := by
  change Finsupp.linearCombination R _ (Finsupp.single ts a) = _
  exact Finsupp.linearCombination_single _ _ _

@[simp]
theorem shuffleRight_ofForest_left [Semiring R] (ts us : PlanarForest) :
    shuffleRight us (ofForest (R := R) ts) = shuffleOf ts us := by
  rw [ofForest, shuffleRight_single_left, one_smul]

@[simp]
theorem shuffleRight_one_left [Semiring R] (us : PlanarForest) :
    shuffleRight (R := R) us 1 = ofForest us := by
  simpa only [ofForest_nil, shuffleOf_nil_left] using
    shuffleRight_ofForest_left (R := R) [] us

/-- Shuffling with the empty forest on the right is the identity. -/
@[simp]
theorem shuffleRight_nil_right [Semiring R] :
    shuffleRight (R := R) [] = LinearMap.id := by
  apply MonoidAlgebra.lhom_ext'
  intro ts
  apply LinearMap.ext_ring
  simp [shuffleRight_single_left, ofForest]

end

end PlanarForestAlgebra

namespace PlanarForest

noncomputable section

variable {R : Type u}

set_option linter.unusedVariables false in
/--
The MKW antipode of an ordered forest, by the recursion of
arXiv:math/0603023, Theorem 2: minus the shuffle products `S_N(p) ⧢ r` over
all MKW coproduct terms `(p, r)` except the full cut.
-/
def mkwAntipode [Ring R] (ω : PlanarForest) : PlanarForestAlgebra R :=
  if h : ω = [] then 1
  else
    -(((mkwTerms ω).tail.attach.map fun pr =>
        PlanarForestAlgebra.shuffleRight pr.1.2 (mkwAntipode pr.1.1)).sum)
termination_by PTree.orderList ω
decreasing_by
  exact orderList_fst_lt_of_mem_tail_mkwTerms h pr.2

@[simp]
theorem mkwAntipode_nil [Ring R] :
    mkwAntipode (R := R) ([] : PlanarForest) = 1 := by
  unfold mkwAntipode
  simp

/-- The defining recursion of the MKW antipode on a nonempty forest. -/
theorem mkwAntipode_of_ne_nil [Ring R] {ω : PlanarForest} (hω : ω ≠ []) :
    mkwAntipode (R := R) ω =
      -(((mkwTerms ω).tail.map fun pr =>
          PlanarForestAlgebra.shuffleRight pr.2 (mkwAntipode (R := R) pr.1)).sum) := by
  conv_lhs => rw [mkwAntipode]
  rw [dite_eq_right hω]
  congr 1
  exact List.sum_attach_map (mkwTerms ω).tail fun pr =>
    PlanarForestAlgebra.shuffleRight pr.2 (mkwAntipode (R := R) pr.1)

/--
The left antipode identity `μ_N(S_N ⊗ I)Δ_N = u_N ∘ e_N` of the MKW Hopf
algebra (arXiv:math/0603023, Theorem 2), evaluated on an ordered forest.
-/
theorem sum_shuffleRight_mkwAntipode_mkwTerms [Ring R] (ω : PlanarForest) :
    ((mkwTerms ω).map fun pr =>
        PlanarForestAlgebra.shuffleRight pr.2 (mkwAntipode (R := R) pr.1)).sum =
      PlanarForestAlgebra.counitCoeff (R := R) ω • 1 := by
  rcases eq_or_ne ω [] with rfl | hω
  · simp
  · rw [mkwTerms_eq_self_nil_cons ω, List.map_cons, List.sum_cons,
      PlanarForestAlgebra.shuffleRight_nil_right, LinearMap.id_apply, mkwAntipode_of_ne_nil hω,
      PlanarForestAlgebra.counitCoeff_ne_nil hω, zero_smul, neg_add_cancel]

/-! ### Small-order verification against arXiv:math/0603023

`S_N(•) = -•` and `S_N(χ) = • ⧢ • - χ = 2(••) - χ` for the two-vertex
chain `χ`.
-/

theorem mkwAntipode_bullet_forest [Ring R] :
    mkwAntipode (R := R) [PTree.bullet] =
      -(PlanarForestAlgebra.ofForest [PTree.bullet]) := by
  rw [mkwAntipode_of_ne_nil (by simp)]
  have htail : (mkwTerms [PTree.bullet]).tail = [([], [PTree.bullet])] := by
    rw [mkwTerms_bullet_forest, List.tail_cons]
  rw [htail]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mkwAntipode_nil,
    PlanarForestAlgebra.shuffleRight_one_left, add_zero]

theorem mkwAntipode_chain2_forest [Ring R] :
    mkwAntipode (R := R) [PTree.chain2] =
      PlanarForestAlgebra.ofForest [PTree.bullet, PTree.bullet] +
        PlanarForestAlgebra.ofForest [PTree.bullet, PTree.bullet] -
        PlanarForestAlgebra.ofForest [PTree.chain2] := by
  rw [mkwAntipode_of_ne_nil (by simp)]
  have htail : (mkwTerms [PTree.chain2]).tail =
      [([PTree.bullet], [PTree.bullet]), ([], [PTree.chain2])] := by
    rw [mkwTerms_chain2_forest, List.tail_cons]
  rw [htail]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    mkwAntipode_bullet_forest, mkwAntipode_nil,
    map_neg,
    PlanarForestAlgebra.shuffleRight_ofForest_left,
    PlanarForestAlgebra.shuffleRight_one_left,
    PlanarForestAlgebra.shuffleOf_singleton_singleton]
  abel

end

end PlanarForest

end HopfAlgebras
