/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.Antipode
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Multiplicativity of the BCK Antipode

The antipode of the commutative BCK Hopf algebra is an algebra morphism:
`S(φψ) = S(φ)S(ψ)`. The proof is by strong induction on total order, using
the convolution identity `μ(S ⊗ I)Δ = u ∘ e`: expanding `μ(S ⊗ I)Δ(φψ)` over
products of coproduct terms and comparing with
`(μ(S ⊗ I)Δφ)(μ(S ⊗ I)Δψ) = 0`, every paired term agrees by the induction
hypothesis except the unique full-cut pair, whose difference is exactly
`S(φψ) - S(φ)S(ψ)`.

## Main definitions

* `RootedForest.antipode_add` - multiplicativity on forest monomials
* `ForestAlgebra.antipode_mul` - multiplicativity on the whole algebra
* `ForestAlgebra.antipodeAlgHom` - the antipode as an algebra homomorphism
-/

namespace HopfAlgebras

universe u

namespace RootedForest

noncomputable section

variable {R : Type u} [CommRing R]

private theorem map_flatMap' {α β γ : Type*} (l : List α) (f : α → List β)
    (g : β → γ) :
    (l.flatMap f).map g = l.flatMap fun a => (f a).map g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem sum_flatMap' {α : Type*} {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem sum_map_sub {α : Type*} {M : Type*} [AddCommGroup M]
    (l : List α) (f g : α → M) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons, ih]
      abel

private theorem sum_mul_sum' {α β : Type*} {M : Type*}
    [NonUnitalNonAssocSemiring M] (xs : List α) (ys : List β)
    (f : α → M) (g : β → M) :
    (xs.map f).sum * (ys.map g).sum =
      (xs.map fun x => (ys.map fun y => f x * g y).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, add_mul, ih, List.map_cons,
        List.sum_cons, List.sum_map_mul_left]

private theorem sum_map_eq_sum_filterMap_map {α : Type*} {M : Type*}
    [AddCommMonoid M] {q : α → Option α}
    (hq : ∀ {x y : α}, q x = some y → y = x) (h : α → M) :
    ∀ l : List α, (∀ x ∈ l, q x = none → h x = 0) →
      (l.map h).sum = ((l.filterMap q).map h).sum
  | [], _ => rfl
  | x :: l, h0 => by
      rw [List.map_cons, List.sum_cons, List.filterMap_cons]
      cases hqx : q x with
      | none =>
          rw [h0 x List.mem_cons_self hqx, zero_add]
          exact sum_map_eq_sum_filterMap_map hq h l
            fun z hz hn => h0 z (List.mem_cons_of_mem _ hz) hn
      | some y =>
          have hyx : y = x := hq hqx
          subst hyx
          rw [List.map_cons, List.sum_cons,
            sum_map_eq_sum_filterMap_map hq h l
              fun z hz hn => h0 z (List.mem_cons_of_mem _ hz) hn]

private theorem rightBoundary_some_eq {x y : RootedForest × RootedForest}
    (h : PTree.rightBoundaryCoproductTerm? x = some y) : y = x := by
  unfold PTree.rightBoundaryCoproductTerm? at h
  by_cases hx : RootedForest.order x.2 = 0
  · rw [if_pos hx] at h
    exact (Option.some_inj.1 h).symm
  · rw [if_neg hx] at h
    cases h

private theorem rightBoundary_none_snd_ne_zero
    {x : RootedForest × RootedForest}
    (h : PTree.rightBoundaryCoproductTerm? x = none) : x.2 ≠ 0 := by
  unfold PTree.rightBoundaryCoproductTerm? at h
  by_cases hx : RootedForest.order x.2 = 0
  · rw [if_pos hx] at h
    cases h
  · intro h0
    rw [h0, RootedForest.order_zero] at hx
    exact hx rfl

private theorem out_map_out_ofPTree_coe' (φ : RootedForest) :
    ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree :
        List RootedTree) : RootedForest) = φ := by
  have hmap :
      (((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree) =
        (Quotient.out φ : List RootedTree) := by
    induction Quotient.out φ with
    | nil => rfl
    | cons τ ts ih =>
        simp [RootedTree.ofPTree_out τ, ih]
  calc ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree :
          List RootedTree) : RootedForest)
      = ((Quotient.out φ : List RootedTree) : RootedForest) := by rw [hmap]
    _ = φ := Quotient.out_eq φ

/-- The forest coproduct has exactly one term with empty right factor,
namely the full cut `φ ⊗ 1`. -/
theorem coproductTerms_filterMap_rightBoundary (φ : RootedForest) :
    (coproductTerms φ).filterMap PTree.rightBoundaryCoproductTerm? =
      [(φ, (0 : RootedForest))] := by
  rw [coproductTerms, PTree.coproductTermsList_rightBoundaryCoproductTerm,
    out_map_out_ofPTree_coe']

/-- The full cut is a coproduct term of every forest. -/
theorem self_zero_mem_coproductTerms (φ : RootedForest) :
    ((φ, (0 : RootedForest)) : RootedForest × RootedForest) ∈
      coproductTerms φ := by
  have hmem : ((φ, (0 : RootedForest)) : RootedForest × RootedForest) ∈
      (coproductTerms φ).filterMap PTree.rightBoundaryCoproductTerm? := by
    rw [coproductTerms_filterMap_rightBoundary]
    exact List.mem_cons_self
  rcases List.mem_filterMap.1 hmem with ⟨a, ha, hqa⟩
  rw [rightBoundary_some_eq hqa]
  exact ha

private theorem antipode_add_aux (n : Nat) :
    ∀ φ ψ : RootedForest, order φ + order ψ ≤ n →
      antipode (R := R) (φ + ψ) = antipode φ * antipode ψ := by
  induction n with
  | zero =>
      intro φ ψ h
      obtain rfl : φ = 0 := (order_eq_zero_iff φ).1 (by omega)
      obtain rfl : ψ = 0 := (order_eq_zero_iff ψ).1 (by omega)
      simp
  | succ n ih =>
      intro φ ψ hle
      by_cases hφ : φ = 0
      · subst hφ
        simp
      by_cases hψ : ψ = 0
      · subst hψ
        simp
      have hφψ : φ + ψ ≠ 0 :=
        (order_pos_iff_ne_zero (φ + ψ)).1 (by
          rw [order_add]
          have := (order_pos_iff_ne_zero φ).2 hφ
          omega)
      -- `μ(S ⊗ I)Δ(φψ) = 0`, expanded over products of coproduct terms.
      have hA :
          ((coproductTerms φ).map fun x =>
            ((coproductTerms ψ).map fun y =>
              antipode (R := R) (x.1 + y.1) *
                ForestAlgebra.ofForest (R := R) (x.2 + y.2)).sum).sum = 0 := by
        have h0 := antipodeLeft_coproduct (R := R) (φ + ψ)
        rw [ForestAlgebra.counitCoeff_ne_zero hφψ, zero_smul, coproduct_add,
          coproduct_eq_sumTerms_coproductTerms φ,
          coproduct_eq_sumTerms_coproductTerms ψ,
          ← ForestTensorAlgebra.sumTerms_multiply,
          ForestTensorAlgebra.antipodeLeft_sumTerms] at h0
        unfold PTree.multiplyCoproductTerms at h0
        rw [map_flatMap', sum_flatMap'] at h0
        simpa [List.map_map, Function.comp_def] using h0
      -- `(μ(S ⊗ I)Δφ) · (μ(S ⊗ I)Δψ) = 0`, expanded the same way.
      have hAφ :
          ((coproductTerms φ).map fun x =>
            antipode (R := R) x.1 * ForestAlgebra.ofForest (R := R) x.2).sum
            = 0 := by
        have h0 := antipodeLeft_coproduct (R := R) φ
        rwa [ForestAlgebra.counitCoeff_ne_zero hφ, zero_smul,
          coproduct_eq_sumTerms_coproductTerms φ,
          ForestTensorAlgebra.antipodeLeft_sumTerms] at h0
      have hAψ :
          ((coproductTerms ψ).map fun y =>
            antipode (R := R) y.1 * ForestAlgebra.ofForest (R := R) y.2).sum
            = 0 := by
        have h0 := antipodeLeft_coproduct (R := R) ψ
        rwa [ForestAlgebra.counitCoeff_ne_zero hψ, zero_smul,
          coproduct_eq_sumTerms_coproductTerms ψ,
          ForestTensorAlgebra.antipodeLeft_sumTerms] at h0
      have hE2 :
          ((coproductTerms φ).map fun x =>
            ((coproductTerms ψ).map fun y =>
              (antipode (R := R) x.1 * ForestAlgebra.ofForest (R := R) x.2) *
                (antipode (R := R) y.1 *
                  ForestAlgebra.ofForest (R := R) y.2)).sum).sum = 0 := by
        rw [← sum_mul_sum', hAφ, zero_mul]
      -- The difference of the two double sums vanishes.
      have hD :
          ((coproductTerms φ).map fun x =>
            ((coproductTerms ψ).map fun y =>
              antipode (R := R) (x.1 + y.1) *
                  ForestAlgebra.ofForest (R := R) (x.2 + y.2) -
                (antipode (R := R) x.1 *
                    ForestAlgebra.ofForest (R := R) x.2) *
                  (antipode (R := R) y.1 *
                    ForestAlgebra.ofForest (R := R) y.2)).sum).sum = 0 := by
        have hsplit :
            ((coproductTerms φ).map fun x =>
              ((coproductTerms ψ).map fun y =>
                antipode (R := R) (x.1 + y.1) *
                    ForestAlgebra.ofForest (R := R) (x.2 + y.2) -
                  (antipode (R := R) x.1 *
                      ForestAlgebra.ofForest (R := R) x.2) *
                    (antipode (R := R) y.1 *
                      ForestAlgebra.ofForest (R := R) y.2)).sum).sum =
              ((coproductTerms φ).map fun x =>
                ((coproductTerms ψ).map fun y =>
                  antipode (R := R) (x.1 + y.1) *
                    ForestAlgebra.ofForest (R := R) (x.2 + y.2)).sum).sum -
                ((coproductTerms φ).map fun x =>
                  ((coproductTerms ψ).map fun y =>
                    (antipode (R := R) x.1 *
                        ForestAlgebra.ofForest (R := R) x.2) *
                      (antipode (R := R) y.1 *
                        ForestAlgebra.ofForest (R := R) y.2)).sum).sum := by
          rw [← sum_map_sub]
          exact congrArg List.sum
            (List.map_congr_left fun x _ => sum_map_sub _ _ _)
        rw [hsplit, hA, hE2, sub_zero]
      -- Pointwise, every pair with a nonempty trunk somewhere vanishes.
      have hpoint : ∀ x ∈ coproductTerms φ, ∀ y ∈ coproductTerms ψ,
          x.2 ≠ 0 ∨ y.2 ≠ 0 →
          antipode (R := R) (x.1 + y.1) *
              ForestAlgebra.ofForest (R := R) (x.2 + y.2) -
            (antipode (R := R) x.1 * ForestAlgebra.ofForest (R := R) x.2) *
              (antipode (R := R) y.1 * ForestAlgebra.ofForest (R := R) y.2) =
            0 := by
        intro x hx y hy hor
        have h1 := coproductTerms_order hx
        have h2 := coproductTerms_order hy
        have hIH : antipode (R := R) (x.1 + y.1) =
            antipode x.1 * antipode y.1 := by
          apply ih
          rcases hor with h | h
          · have hpos := (order_pos_iff_ne_zero x.2).2 h
            omega
          · have hpos := (order_pos_iff_ne_zero y.2).2 h
            omega
        rw [hIH, ForestAlgebra.ofForest_add, sub_eq_zero]
        ring
      -- Extract the unique full-cut pair from the vanishing double sum.
      have houter : ∀ x ∈ coproductTerms φ,
          PTree.rightBoundaryCoproductTerm? x = none →
          ((coproductTerms ψ).map fun y =>
            antipode (R := R) (x.1 + y.1) *
                ForestAlgebra.ofForest (R := R) (x.2 + y.2) -
              (antipode (R := R) x.1 *
                  ForestAlgebra.ofForest (R := R) x.2) *
                (antipode (R := R) y.1 *
                  ForestAlgebra.ofForest (R := R) y.2)).sum = 0 := by
        intro x hx hnone
        apply List.sum_eq_zero
        intro z hz
        rcases List.mem_map.1 hz with ⟨y, hy, rfl⟩
        exact hpoint x hx y hy (Or.inl (rightBoundary_none_snd_ne_zero hnone))
      rw [sum_map_eq_sum_filterMap_map
          (fun {x y} h => rightBoundary_some_eq h) _ (coproductTerms φ) houter,
        coproductTerms_filterMap_rightBoundary] at hD
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero] at hD
      have hinner : ∀ y ∈ coproductTerms ψ,
          PTree.rightBoundaryCoproductTerm? y = none →
          antipode (R := R) (φ + y.1) *
              ForestAlgebra.ofForest (R := R) ((0 : RootedForest) + y.2) -
            (antipode (R := R) φ *
                ForestAlgebra.ofForest (R := R) (0 : RootedForest)) *
              (antipode (R := R) y.1 *
                ForestAlgebra.ofForest (R := R) y.2) = 0 := by
        intro y hy hnone
        exact hpoint (φ, 0) (self_zero_mem_coproductTerms φ) y hy
          (Or.inr (rightBoundary_none_snd_ne_zero hnone))
      rw [sum_map_eq_sum_filterMap_map
          (fun {x y} h => rightBoundary_some_eq h) _ (coproductTerms ψ) hinner,
        coproductTerms_filterMap_rightBoundary] at hD
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, ForestAlgebra.ofForest_zero, mul_one] at hD
      exact sub_eq_zero.1 hD

/-- The BCK antipode is multiplicative on forest monomials:
`S(φψ) = S(φ)S(ψ)`. -/
theorem antipode_add (φ ψ : RootedForest) :
    antipode (R := R) (φ + ψ) = antipode φ * antipode ψ :=
  antipode_add_aux (order φ + order ψ) φ ψ le_rfl

private theorem mem_support_list_sum {l : List (ForestAlgebra R)}
    {ψ : RootedForest} (h : ψ ∈ l.sum.coeff.support) :
    ∃ x ∈ l, ψ ∈ x.coeff.support := by
  classical
  induction l with
  | nil =>
      rw [List.sum_nil] at h
      exact absurd rfl (Finsupp.mem_support_iff.1 h)
  | cons a l ih =>
      rw [List.sum_cons, AddMonoidAlgebra.coeff_add] at h
      rcases Finset.mem_union.1 (Finsupp.support_add h) with h' | h'
      · exact ⟨a, List.mem_cons_self, h'⟩
      · obtain ⟨x, hx, hψ⟩ := ih h'
        exact ⟨x, List.mem_cons_of_mem _ hx, hψ⟩

private theorem mem_support_neg {x : ForestAlgebra R} {ψ : RootedForest}
    (h : ψ ∈ (-x).coeff.support) : ψ ∈ x.coeff.support := by
  rw [Finsupp.mem_support_iff] at h ⊢
  intro h0
  apply h
  rw [show (-x).coeff ψ = -(x.coeff ψ) from rfl, h0, neg_zero]

private theorem antipode_support_aux (n : ℕ) :
    ∀ φ : RootedForest, order φ ≤ n →
      ∀ ψ ∈ (antipode (R := R) φ).coeff.support, order ψ = order φ := by
  classical
  induction n with
  | zero =>
      intro φ h ψ hψ
      have hφ : φ = 0 := (order_eq_zero_iff φ).1 (by omega)
      subst hφ
      rw [antipode_zero] at hψ
      have : ψ ∈ (AddMonoidAlgebra.single (0 : RootedForest) (1 : R)).coeff.support := by
        simpa [AddMonoidAlgebra.one_def] using hψ
      have hψ0 : ψ = 0 := Finset.mem_singleton.1
        (Finsupp.support_single_subset this)
      rw [hψ0]
  | succ n ih =>
      intro φ h ψ hψ
      by_cases hφ : φ = 0
      · subst hφ
        rw [antipode_zero] at hψ
        have : ψ ∈ (AddMonoidAlgebra.single (0 : RootedForest) (1 : R)).coeff.support := by
          simpa [AddMonoidAlgebra.one_def] using hψ
        have hψ0 : ψ = 0 := Finset.mem_singleton.1
          (Finsupp.support_single_subset this)
        rw [hψ0]
      · rw [antipode_eq_of_ne_zero hφ, sub_eq_add_neg, AddMonoidAlgebra.coeff_add] at hψ
        rcases Finset.mem_union.1 (Finsupp.support_add hψ) with h' | h'
        · have h'' := mem_support_neg h'
          have : ψ = φ := Finset.mem_singleton.1
            (Finsupp.support_single_subset h'')
          rw [this]
        · have h'' := mem_support_neg h'
          rw [antipodeProperSum] at h''
          obtain ⟨x, hx, hψx⟩ := mem_support_list_sum h''
          rcases List.mem_map.1 hx with ⟨term, hterm, rfl⟩
          have hmem : term.1 ∈ properCoproductTerms φ := term.2
          have hsupp := AddMonoidAlgebra.support_coeff_mul_subset
            (antipode (R := R) term.1.1)
            (ForestAlgebra.ofForest (R := R) term.1.2)
          obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (hsupp hψx)
          have hleft : order term.1.1 < order φ :=
            properCoproductTerms_left_order_lt hmem
          have ha_ord : order a = order term.1.1 :=
            ih term.1.1 (by omega) a ha
          have hb_ord : b = term.1.2 := Finset.mem_singleton.1
            (Finsupp.support_single_subset hb)
          have hgrade := properCoproductTerms_order hmem
          rw [order_add, ha_ord, hb_ord]
          omega

/-- The BCK antipode preserves the order grading: `S(φ)` is supported on
forests of the same order as `φ`. -/
theorem order_eq_of_mem_support_antipode {φ ψ : RootedForest}
    (hψ : ψ ∈ (antipode (R := R) φ).coeff.support) : order ψ = order φ :=
  antipode_support_aux (order φ) φ le_rfl ψ hψ

end

end RootedForest

namespace ForestAlgebra

noncomputable section

variable {R : Type u} [CommRing R]

/-- The linear antipode preserves the unit. -/
theorem antipode_one : antipode (R := R) (1 : ForestAlgebra R) = 1 := by
  calc antipode (R := R) (1 : ForestAlgebra R)
      = antipode (ofForest (R := R) 0) := by rw [ofForest_zero]
    _ = RootedForest.antipode (R := R) 0 := antipode_ofForest 0
    _ = 1 := RootedForest.antipode_zero

/-- The BCK antipode is an algebra morphism, since the BCK Hopf algebra is
commutative. -/
theorem antipode_mul (x y : ForestAlgebra R) :
    antipode (R := R) (x * y) = antipode x * antipode y := by
  refine AddMonoidAlgebra.induction_on (x := x)
    (motive := fun x => antipode (R := R) (x * y) = antipode x * antipode y)
    ?_ ?_ ?_
  · intro φ
    change antipode (R := R) (ofForest (R := R) φ * y) =
      antipode (ofForest (R := R) φ) * antipode y
    refine AddMonoidAlgebra.induction_on (x := y)
      (motive := fun y => antipode (R := R) (ofForest (R := R) φ * y) =
        antipode (ofForest (R := R) φ) * antipode y)
      ?_ ?_ ?_
    · intro ψ
      change antipode (R := R) (ofForest (R := R) φ * ofForest (R := R) ψ) =
        antipode (ofForest (R := R) φ) * antipode (ofForest (R := R) ψ)
      rw [← ofForest_add, antipode_ofForest, antipode_ofForest,
        antipode_ofForest, RootedForest.antipode_add]
    · intro y₁ y₂ h₁ h₂
      rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
    · intro r y hy
      rw [mul_smul_comm, map_smul, hy, map_smul, mul_smul_comm]
  · intro x₁ x₂ h₁ h₂
    rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  · intro r x hx
    rw [smul_mul_assoc, map_smul, hx, map_smul, smul_mul_assoc]

/-- The BCK antipode as an algebra homomorphism. -/
def antipodeAlgHom (R : Type u) [CommRing R] :
    ForestAlgebra R →ₐ[R] ForestAlgebra R :=
  AlgHom.ofLinearMap (antipode (R := R)) antipode_one antipode_mul

@[simp]
theorem antipodeAlgHom_apply (x : ForestAlgebra R) :
    antipodeAlgHom R x = antipode (R := R) x :=
  rfl

end

end ForestAlgebra

end HopfAlgebras
