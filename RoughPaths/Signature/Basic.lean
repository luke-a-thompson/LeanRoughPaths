/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Words.Shuffle
import HopfAlgebras.Combinatorial.Shuffle
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

/-!
# Word Signatures

This file defines the word-indexed algebraic signature data used in rough path
theory. It covers the shuffle identity for group-like signatures and finite
degree truncations.

## Main definitions

* raw word series `List α → R` - formal coefficient families indexed by words
* `Word.comapMapLetters` - relabel word-indexed series by mapping letters
* `Word.shuffleCoeff` - finite shuffle sum of coefficients
* `Word.IsGroupLike` - the shuffle identity for signatures
* `Word.tensorProduct` - concatenation product of signature series
* `Word.Truncation` - coefficients restricted to words of length at most `n`
* `Word.SatisfiesShuffleUpToDegree` - finite-degree shuffle identity
* `Signature` - bundled group-like signature series

## References

* Terry Lyons, Michael Caruana, Thierry Levy,
  *Differential Equations Driven by Rough Paths*
* Peter Friz, Nicolas Victoir, *Multidimensional Stochastic Processes as Rough Paths*
-/

namespace RoughPaths

open HopfAlgebras

universe u v w z

namespace Word

variable {α : Type u} {β : Type v} {R : Type w}

/-- The coefficient of a word in a formal signature series. -/
def coeff (a : (List α → R)) (w : List α) : R :=
  a w

@[simp]
theorem coeff_apply (a : (List α → R)) (w : List α) :
    coeff a w = a w :=
  rfl

@[ext]
theorem ext {a b : (List α → R)}
    (h : ∀ w, coeff a w = coeff b w) : a = b := by
  funext w
  exact h w

/-- The coefficient of the empty word. -/
def emptyCoeff (a : (List α → R)) : R :=
  coeff a []

@[simp]
theorem coeff_nil (a : (List α → R)) :
    coeff a [] = emptyCoeff a :=
  rfl

/-- Unit empty-word coefficient condition. -/
def HasUnitEmpty [One R] (a : (List α → R)) : Prop :=
  emptyCoeff a = 1

theorem HasUnitEmpty.coeff_nil [One R] {a : (List α → R)}
    (h : HasUnitEmpty a) : coeff a [] = 1 :=
  h

/-- Relabel a word-indexed series. -/
def comapMapLetters {γ : Type u} {δ : Type v}
    (f : γ → δ) (a : (List δ → R)) : (List γ → R) :=
  fun w => a (w.map f)

@[simp]
theorem coeff_comapMapLetters {γ : Type u} {δ : Type v}
    (f : γ → δ) (a : (List δ → R)) (w : List γ) :
    coeff (comapMapLetters f a) w = coeff a (w.map f) :=
  rfl

theorem HasUnitEmpty.comapMapLetters {γ : Type u} {δ : Type v} [One R]
    {a : (List δ → R)} (h : HasUnitEmpty a) (f : γ → δ) :
    HasUnitEmpty (comapMapLetters f a) := by
  exact h

@[simp]
theorem comapMapLetters_id (a : (List α → R)) :
    comapMapLetters id a = a := by
  ext w
  simp [comapMapLetters]

theorem comapMapLetters_comp {γ : Type u} {δ : Type v} {ε : Type z}
    (f : γ → δ) (g : δ → ε) (a : (List ε → R)) :
    comapMapLetters f (comapMapLetters g a) = comapMapLetters (g ∘ f) a := by
  ext word
  simp [comapMapLetters, List.map_map, Function.comp_def]

/-- The unit signature series. -/
def unit (α : Type u) (R : Type v) [Zero R] [One R] : (List α → R)
  | [] => 1
  | _ :: _ => 0

@[simp]
theorem coeff_unit_nil [Zero R] [One R] :
    coeff (unit α R) [] = 1 :=
  rfl

@[simp]
theorem coeff_unit_cons [Zero R] [One R] (x : α) (w : List α) :
    coeff (unit α R) (x :: w) = 0 :=
  rfl

theorem unit_hasUnitEmpty [Zero R] [One R] :
    HasUnitEmpty (unit α R) :=
  rfl

@[simp]
theorem comapMapLetters_unit {γ : Type u} {δ : Type v} [Zero R] [One R]
    (f : γ → δ) :
    comapMapLetters f (unit δ R) = unit γ R := by
  ext word
  cases word <;> simp [comapMapLetters, unit]

/-- Sum of coefficients over all shuffles of two words. -/
def shuffleCoeff [AddMonoid R] (a : (List α → R))
    (u v : List α) : R :=
  ((Word.shuffle u v).map a).sum

@[simp]
theorem shuffleCoeff_nil_left [AddMonoid R]
    (a : (List α → R)) (v : List α) :
    shuffleCoeff a [] v = coeff a v := by
  simp [shuffleCoeff]

@[simp]
theorem shuffleCoeff_nil_right [AddMonoid R]
    (a : (List α → R)) (u : List α) :
    shuffleCoeff a u [] = coeff a u := by
  simp [shuffleCoeff]

theorem shuffleCoeff_comapMapLetters {γ : Type u} {δ : Type v} [AddMonoid R]
    (f : γ → δ) (a : (List δ → R)) (u v : List γ) :
    shuffleCoeff (comapMapLetters f a) u v = shuffleCoeff a (u.map f) (v.map f) := by
  have h := congrArg (fun ws : List (List δ) => (ws.map a).sum) (Word.shuffle_map f u v)
  change
    ((Word.shuffle u v).map (fun w => a (w.map f))).sum =
      ((Word.shuffle (u.map f) (v.map f)).map a).sum
  simpa [List.map_map, Function.comp_def] using h

private theorem sum_unit_cons [AddMonoid R] [One R]
    (x : α) (ws : List (List α)) :
    ((ws.map (unit α R ∘ fun w => x :: w)).sum) = 0 := by
  induction ws with
  | nil =>
      rfl
  | cons w ws ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp [Function.comp, unit]

theorem shuffleCoeff_unit [Semiring R] (u v : List α) :
    shuffleCoeff (unit α R) u v = unit α R u * unit α R v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil =>
          simp [shuffleCoeff, unit]
      | cons y v =>
          simp [shuffleCoeff, unit]
  | cons x u ih =>
      cases v with
      | nil =>
          simp [shuffleCoeff, unit]
      | cons y v =>
          simp [shuffleCoeff, List.map_append, List.map_map, sum_unit_cons, unit]

/-- A signature series satisfying the shuffle identity. -/
def IsGroupLike [Semiring R] (a : (List α → R)) : Prop :=
  coeff a [] = 1 ∧ ∀ u v : List α, coeff a u * coeff a v = shuffleCoeff a u v

theorem IsGroupLike.coeff_nil [Semiring R] {a : (List α → R)}
    (h : IsGroupLike a) : coeff a [] = 1 :=
  h.1

theorem IsGroupLike.shuffle [Semiring R] {a : (List α → R)}
    (h : IsGroupLike a) (u v : List α) :
    coeff a u * coeff a v = shuffleCoeff a u v :=
  h.2 u v

theorem unit_isGroupLike [Semiring R] :
    IsGroupLike (unit α R) := by
  constructor
  · rfl
  · intro u v
    simpa [coeff] using (shuffleCoeff_unit (α := α) (R := R) u v).symm

theorem IsGroupLike.comapMapLetters {γ : Type u} {δ : Type v} [Semiring R]
    {a : (List δ → R)} (h : IsGroupLike a) (f : γ → δ) :
    IsGroupLike (comapMapLetters f a) := by
  constructor
  · exact h.coeff_nil
  · intro u v
    rw [coeff_comapMapLetters, coeff_comapMapLetters, h.shuffle (u.map f) (v.map f)]
    exact (shuffleCoeff_comapMapLetters f a u v).symm

/-- Concatenation, or tensor, product of two word-indexed series. -/
def tensorProduct [AddMonoid R] [Mul R]
    (a b : (List α → R)) : (List α → R) :=
  fun w => ((Word.splits w).map fun p => coeff a p.1 * coeff b p.2).sum

@[simp]
theorem tensorProduct_nil [AddMonoid R] [Mul R]
    (a b : (List α → R)) :
    coeff (tensorProduct a b) [] = coeff a [] * coeff b [] := by
  simp [tensorProduct]

theorem tensorProduct_cons [AddMonoid R] [Mul R]
    (a b : (List α → R)) (x : α) (w : List α) :
    coeff (tensorProduct a b) (x :: w) =
      coeff a [] * coeff b (x :: w) +
        ((Word.splits w).map fun p => coeff a (x :: p.1) * coeff b p.2).sum := by
  change ((Word.splits (x :: w)).map fun p => coeff a p.1 * coeff b p.2).sum =
    coeff a [] * coeff b (x :: w) +
      ((Word.splits w).map fun p => coeff a (x :: p.1) * coeff b p.2).sum
  rw [Word.splits_cons, List.map_cons, List.sum_cons, List.map_map]
  change
    coeff a [] * coeff b (x :: w) +
        ((Word.splits w).map fun p => coeff a (x :: p.1) * coeff b p.2).sum =
      coeff a [] * coeff b (x :: w) +
        ((Word.splits w).map fun p => coeff a (x :: p.1) * coeff b p.2).sum
  rfl

theorem tensorProduct_comapMapLetters {γ : Type u} {δ : Type v} [AddMonoid R] [Mul R]
    (f : γ → δ) (a b : (List δ → R)) :
    tensorProduct (comapMapLetters f a) (comapMapLetters f b) =
      comapMapLetters f (tensorProduct a b) := by
  ext word
  have h := congrArg
    (fun ps : List (List δ × List δ) =>
      (ps.map fun p => coeff a p.1 * coeff b p.2).sum)
    (Word.splits_map f word)
  change
    ((Word.splits word).map fun p =>
      coeff a (p.1.map f) * coeff b (p.2.map f)).sum =
        ((Word.splits (word.map f)).map fun p => coeff a p.1 * coeff b p.2).sum
  simpa [List.map_map, Function.comp_def] using h

private theorem sum_unit_mul_cons_pairs [Semiring R]
    (a : (List α → R)) (x : α) :
    ∀ ps : List (List α × List α),
      ((ps.map fun p => coeff (unit α R) (x :: p.1) * coeff a p.2).sum) = 0
  | [] => rfl
  | p :: ps => by
      rw [List.map_cons, List.sum_cons, sum_unit_mul_cons_pairs a x ps]
      simp [unit, coeff]

private theorem sum_unit_mul_splits [Semiring R]
    (a : (List α → R)) :
    ∀ w : List α,
      ((Word.splits w).map fun p =>
        coeff (unit α R) p.1 * coeff a p.2).sum = coeff a w
  | [] => by
      simp [unit, coeff]
  | x :: w => by
      rw [Word.splits_cons, List.map_cons, List.sum_cons]
      have htail :
          ((List.map (fun p : List α × List α => (x :: p.1, p.2)) (Word.splits w)).map
              fun p => coeff (unit α R) p.1 * coeff a p.2).sum = 0 := by
        induction Word.splits w with
        | nil =>
            rfl
        | cons p ps ih =>
            rw [List.map_cons, List.map_cons, List.sum_cons, ih]
            simp [unit, coeff]
      rw [htail]
      simp [unit, coeff]

private theorem sum_mul_unit_splits [Semiring R]
    (a : (List α → R)) (pref suffix : List α) :
    ((Word.splits suffix).map fun p =>
      coeff a (pref ++ p.1) * coeff (unit α R) p.2).sum =
        coeff a (pref ++ suffix) := by
  induction suffix generalizing pref with
  | nil =>
      simp [unit, coeff]
  | cons x suffix ih =>
      rw [Word.splits_cons, List.map_cons, List.sum_cons]
      rw [show coeff a (pref ++ []) * coeff (unit α R) (x :: suffix) = 0 by
        simp [unit, coeff]]
      simp only [zero_add]
      simp only [List.map_map]
      have h := ih (pref ++ [x])
      change
        ((Word.splits suffix).map fun p =>
          coeff a (pref ++ x :: p.1) * coeff (unit α R) p.2).sum =
            coeff a (pref ++ x :: suffix)
      simpa [List.append_assoc] using h

@[simp]
theorem tensorProduct_unit_left [Semiring R] (a : (List α → R)) :
    tensorProduct (unit α R) a = a := by
  ext w
  simpa [tensorProduct] using sum_unit_mul_splits a w

@[simp]
theorem tensorProduct_unit_right [Semiring R] (a : (List α → R)) :
    tensorProduct a (unit α R) = a := by
  ext w
  simpa [tensorProduct] using sum_mul_unit_splits a [] w

theorem tensorProduct_hasUnitEmpty [Semiring R]
    {a b : (List α → R)}
    (ha : HasUnitEmpty a) (hb : HasUnitEmpty b) :
    HasUnitEmpty (tensorProduct a b) := by
  change coeff (tensorProduct a b) [] = 1
  rw [tensorProduct_nil]
  change coeff a [] = 1 at ha
  change coeff b [] = 1 at hb
  rw [ha, hb]
  simp

private theorem tensorProduct_left_assoc_coeff [Semiring R]
    (a b c : (List α → R)) (w : List α) :
    coeff (tensorProduct (tensorProduct a b) c) w =
      ((Word.leftSplits3 w).map fun p =>
        (coeff a p.1 * coeff b p.2.1) * coeff c p.2.2).sum := by
  change
    ((Word.splits w).map fun p =>
      ((Word.splits p.1).map fun q => coeff a q.1 * coeff b q.2).sum *
        coeff c p.2).sum =
    ((Word.leftSplits3 w).map fun p =>
      (coeff a p.1 * coeff b p.2.1) * coeff c p.2.2).sum
  have hleft :
      ((Word.splits w).map fun p =>
        ((Word.splits p.1).map fun q => coeff a q.1 * coeff b q.2).sum *
          coeff c p.2).sum =
        ((Word.splits w).map fun p =>
          ((Word.splits p.1).map fun q =>
            (coeff a q.1 * coeff b q.2) * coeff c p.2).sum).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    exact (List.sum_map_mul_right (Word.splits p.1)
      (fun q => coeff a q.1 * coeff b q.2) (coeff c p.2)).symm
  rw [hleft]
  have hflatten := (List.sum_flatten (l := ((Word.splits w).map fun p =>
      ((Word.splits p.1).map fun q =>
        (coeff a q.1 * coeff b q.2) * coeff c p.2) : List (List R))))
  have htarget :
      ((Word.splits w).flatMap fun p =>
        (Word.splits p.1).map fun q =>
          (coeff a q.1 * coeff b q.2) * coeff c p.2).sum =
        ((Word.splits w).map fun p =>
          ((Word.splits p.1).map fun q =>
            (coeff a q.1 * coeff b q.2) * coeff c p.2).sum).sum := by
    convert hflatten using 1 <;>
      simp [List.flatMap, Function.comp_def]
  simpa [Word.leftSplits3, List.map_flatMap, Function.comp_def] using htarget.symm

private theorem tensorProduct_right_assoc_coeff [Semiring R]
    (a b c : (List α → R)) (w : List α) :
    coeff (tensorProduct a (tensorProduct b c)) w =
      ((Word.rightSplits3 w).map fun p =>
        coeff a p.1 * (coeff b p.2.1 * coeff c p.2.2)).sum := by
  change
    ((Word.splits w).map fun p =>
      coeff a p.1 *
        ((Word.splits p.2).map fun q => coeff b q.1 * coeff c q.2).sum).sum =
    ((Word.rightSplits3 w).map fun p =>
      coeff a p.1 * (coeff b p.2.1 * coeff c p.2.2)).sum
  have hright :
      ((Word.splits w).map fun p =>
        coeff a p.1 *
          ((Word.splits p.2).map fun q => coeff b q.1 * coeff c q.2).sum).sum =
        ((Word.splits w).map fun p =>
          ((Word.splits p.2).map fun q =>
            coeff a p.1 * (coeff b q.1 * coeff c q.2)).sum).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    exact (List.sum_map_mul_left (Word.splits p.2)
      (fun q => coeff b q.1 * coeff c q.2) (coeff a p.1)).symm
  rw [hright]
  have hflatten := (List.sum_flatten (l := ((Word.splits w).map fun p =>
      ((Word.splits p.2).map fun q =>
        coeff a p.1 * (coeff b q.1 * coeff c q.2)) : List (List R))))
  have htarget :
      ((Word.splits w).flatMap fun p =>
        (Word.splits p.2).map fun q =>
          coeff a p.1 * (coeff b q.1 * coeff c q.2)).sum =
        ((Word.splits w).map fun p =>
          ((Word.splits p.2).map fun q =>
            coeff a p.1 * (coeff b q.1 * coeff c q.2)).sum).sum := by
    convert hflatten using 1 <;>
      simp [List.flatMap, Function.comp_def]
  simpa [Word.rightSplits3, List.map_flatMap, Function.comp_def] using htarget.symm

theorem tensorProduct_assoc [Semiring R]
    (a b c : (List α → R)) :
    tensorProduct (tensorProduct a b) c =
      tensorProduct a (tensorProduct b c) := by
  ext w
  rw [tensorProduct_left_assoc_coeff, tensorProduct_right_assoc_coeff]
  calc
    ((Word.leftSplits3 w).map fun p =>
        (coeff a p.1 * coeff b p.2.1) * coeff c p.2.2).sum =
      ((Word.rightSplits3 w).map fun p =>
        (coeff a p.1 * coeff b p.2.1) * coeff c p.2.2).sum := by
        exact ((Word.leftSplits3_perm_rightSplits3 w).map
          fun p => (coeff a p.1 * coeff b p.2.1) * coeff c p.2.2).sum_eq
    _ = ((Word.rightSplits3 w).map fun p =>
        coeff a p.1 * (coeff b p.2.1 * coeff c p.2.2)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro p _hp
        rw [mul_assoc]

/-- Truncation of a signature series to words of length at most `n`. -/
abbrev Truncation (α : Type u) (R : Type v) (n : Nat) : Type (max u v) :=
  {w : List α // w.length ≤ n} → R

/-- Restrict a signature series to words of length at most `n`. -/
def truncate (a : (List α → R)) (n : Nat) : Truncation α R n :=
  fun w => coeff a w.1

@[simp]
theorem truncate_apply (a : (List α → R)) (n : Nat)
    (w : {w : List α // w.length ≤ n}) :
    truncate a n w = coeff a w.1 :=
  rfl

theorem truncate_ext {a b : (List α → R)} {n : Nat}
    (h : ∀ w : List α, w.length ≤ n → coeff a w = coeff b w) :
    truncate a n = truncate b n := by
  funext w
  exact h w.1 w.2

theorem truncate_eq_iff_agreeUpToDegree (a b : (List α → R)) (n : Nat) :
    truncate a n = truncate b n ↔
      ∀ w : List α, w.length ≤ n → coeff a w = coeff b w := by
  constructor
  · intro h w hw
    exact congrFun h ⟨w, hw⟩
  · exact truncate_ext

theorem truncate_comapMapLetters {γ : Type u} {δ : Type v}
    (f : γ → δ) (a : (List δ → R)) (n : Nat) :
    truncate (comapMapLetters f a) n =
      fun w : {w : List γ // w.length ≤ n} => coeff a (w.1.map f) := rfl

/-- Agreement of two signature series through word degree `n`. -/
def AgreeUpToDegree (a b : (List α → R)) (n : Nat) : Prop :=
  ∀ w : List α, w.length ≤ n → coeff a w = coeff b w

theorem agreeUpToDegree_refl (a : (List α → R)) (n : Nat) :
    AgreeUpToDegree a a n := by
  intro w hw
  rfl

theorem AgreeUpToDegree.symm {a b : (List α → R)} {n : Nat}
    (h : AgreeUpToDegree a b n) : AgreeUpToDegree b a n := by
  intro w hw
  exact (h w hw).symm

theorem AgreeUpToDegree.trans {a b c : (List α → R)} {n : Nat}
    (hab : AgreeUpToDegree a b n) (hbc : AgreeUpToDegree b c n) :
    AgreeUpToDegree a c n := by
  intro w hw
  exact (hab w hw).trans (hbc w hw)

theorem AgreeUpToDegree.mono {a b : (List α → R)} {m n : Nat}
    (h : AgreeUpToDegree a b n) (hmn : m ≤ n) :
    AgreeUpToDegree a b m := by
  intro w hw
  exact h w (hw.trans hmn)

theorem AgreeUpToDegree.comapMapLetters {γ : Type u} {δ : Type v}
    {a b : (List δ → R)} {n : Nat}
    (h : AgreeUpToDegree a b n) (f : γ → δ) :
    AgreeUpToDegree (comapMapLetters f a) (comapMapLetters f b) n := by
  intro word hword
  rw [coeff_comapMapLetters, coeff_comapMapLetters]
  exact h (word.map f) (by simpa using hword)

theorem agreeUpToDegree_succ_iff {a b : (List α → R)} {n : Nat} :
    AgreeUpToDegree a b (n + 1) ↔
      AgreeUpToDegree a b n ∧
        ∀ w : List α, w.length = n + 1 → coeff a w = coeff b w := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun w hw => h w (by omega)⟩
  · rintro ⟨hprev, htop⟩ w hw
    by_cases hle : w.length ≤ n
    · exact hprev w hle
    · exact htop w (by omega)

theorem agreeUpToDegree_of_eq {a b : (List α → R)}
    (h : a = b) (n : Nat) : AgreeUpToDegree a b n := by
  subst b
  exact agreeUpToDegree_refl a n

theorem eq_of_agreeUpToDegree_all {a b : (List α → R)}
    (h : ∀ n, AgreeUpToDegree a b n) : a = b := by
  funext w
  exact h w.length w le_rfl

theorem agreeUpToDegree_all_iff_eq {a b : (List α → R)} :
    (∀ n, AgreeUpToDegree a b n) ↔ a = b := by
  constructor
  · exact eq_of_agreeUpToDegree_all
  · intro h n
    exact agreeUpToDegree_of_eq h n

theorem truncate_eq_iff (a b : (List α → R)) (n : Nat) :
    truncate a n = truncate b n ↔ AgreeUpToDegree a b n :=
  truncate_eq_iff_agreeUpToDegree a b n

theorem agreeUpToDegree_tensorProduct [AddMonoid R] [Mul R]
    {a a' b b' : (List α → R)} {n : Nat}
    (ha : AgreeUpToDegree a a' n) (hb : AgreeUpToDegree b b' n) :
    AgreeUpToDegree (tensorProduct a b) (tensorProduct a' b') n := by
  intro w hw
  change
    ((Word.splits w).map fun p => coeff a p.1 * coeff b p.2).sum =
      ((Word.splits w).map fun p => coeff a' p.1 * coeff b' p.2).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have happend := Word.mem_splits_append hp
  have hlength : p.1.length + p.2.length = w.length := by
    have := congrArg List.length happend
    simpa [List.length_append] using this
  have hp₁ : p.1.length ≤ n := by omega
  have hp₂ : p.2.length ≤ n := by omega
  rw [ha p.1 hp₁, hb p.2 hp₂]

theorem agreeUpToDegree_tensorProduct_left [AddMonoid R] [Mul R]
    {a a' b : (List α → R)} {n : Nat}
    (ha : AgreeUpToDegree a a' n) :
    AgreeUpToDegree (tensorProduct a b) (tensorProduct a' b) n :=
  agreeUpToDegree_tensorProduct ha (agreeUpToDegree_refl b n)

theorem agreeUpToDegree_tensorProduct_right [AddMonoid R] [Mul R]
    {a b b' : (List α → R)} {n : Nat}
    (hb : AgreeUpToDegree b b' n) :
    AgreeUpToDegree (tensorProduct a b) (tensorProduct a b') n :=
  agreeUpToDegree_tensorProduct (agreeUpToDegree_refl a n) hb

theorem tensorProduct_eq_of_agreeUpToDegree_all [AddMonoid R] [Mul R]
    {a a' b b' : (List α → R)}
    (ha : ∀ n, AgreeUpToDegree a a' n)
    (hb : ∀ n, AgreeUpToDegree b b' n) :
    tensorProduct a b = tensorProduct a' b' :=
  eq_of_agreeUpToDegree_all fun n => agreeUpToDegree_tensorProduct (ha n) (hb n)

theorem tensorProduct_left_eq_of_agreeUpToDegree_all [AddMonoid R] [Mul R]
    {a a' b : (List α → R)}
    (ha : ∀ n, AgreeUpToDegree a a' n) :
    tensorProduct a b = tensorProduct a' b :=
  tensorProduct_eq_of_agreeUpToDegree_all ha fun n => agreeUpToDegree_refl b n

theorem tensorProduct_right_eq_of_agreeUpToDegree_all [AddMonoid R] [Mul R]
    {a b b' : (List α → R)}
    (hb : ∀ n, AgreeUpToDegree b b' n) :
    tensorProduct a b = tensorProduct a b' :=
  tensorProduct_eq_of_agreeUpToDegree_all (fun n => agreeUpToDegree_refl a n) hb

/-- The shuffle identity restricted to pairs with total degree at most `n`. -/
def SatisfiesShuffleUpToDegree [Semiring R]
    (a : (List α → R)) (n : Nat) : Prop :=
  coeff a [] = 1 ∧
    ∀ u v : List α, u.length + v.length ≤ n →
      coeff a u * coeff a v = shuffleCoeff a u v

theorem IsGroupLike.satisfiesShuffleUpToDegree [Semiring R]
    {a : (List α → R)} (h : IsGroupLike a) (n : Nat) :
    SatisfiesShuffleUpToDegree a n :=
  ⟨h.coeff_nil, fun u v _ => h.shuffle u v⟩

theorem SatisfiesShuffleUpToDegree.mono [Semiring R]
    {a : (List α → R)} {m n : Nat}
    (h : SatisfiesShuffleUpToDegree a n) (hmn : m ≤ n) :
    SatisfiesShuffleUpToDegree a m :=
  ⟨h.1, fun u v huv => h.2 u v (huv.trans hmn)⟩

theorem SatisfiesShuffleUpToDegree.comapMapLetters {γ : Type u} {δ : Type v}
    [Semiring R] {a : (List δ → R)} {n : Nat}
    (h : SatisfiesShuffleUpToDegree a n) (f : γ → δ) :
    SatisfiesShuffleUpToDegree (comapMapLetters f a) n := by
  constructor
  · exact h.1
  · intro u v huv
    rw [coeff_comapMapLetters, coeff_comapMapLetters]
    rw [h.2 (u.map f) (v.map f) (by simpa using huv)]
    exact (shuffleCoeff_comapMapLetters f a u v).symm

theorem isGroupLike_iff_satisfiesShuffleUpToDegree_all [Semiring R]
    {a : (List α → R)} :
    IsGroupLike a ↔ ∀ n, SatisfiesShuffleUpToDegree a n := by
  constructor
  · intro h n
    exact h.satisfiesShuffleUpToDegree n
  · intro h
    constructor
    · exact (h 0).1
    · intro u v
      exact (h (u.length + v.length)).2 u v le_rfl

theorem unit_satisfiesShuffleUpToDegree [Semiring R] (n : Nat) :
    SatisfiesShuffleUpToDegree (unit α R) n :=
  unit_isGroupLike.satisfiesShuffleUpToDegree n

end Word

/-- **Group-like signature series are exactly the characters of the word
shuffle Hopf algebra** — definitionally. -/
theorem isCharacter_wordHopf_iff {α : Type u} {R : Type v}
    [CommSemiring R] (φ : List α → R) :
    (wordHopf α).IsCharacter φ ↔ Word.IsGroupLike φ :=
  Iff.rfl

/-- The tensor (Chen) product of series is the convolution product dual
to deconcatenation — definitionally. -/
theorem tensorProduct_eq_conv {α : Type u} {R : Type v}
    [CommSemiring R] (A B : (List α → R)) :
    Word.tensorProduct A B =
      CombBialg.Character.conv (H := (wordHopf α).toCombBialg) A B :=
  rfl

/-- A signature: a **character of the word shuffle Hopf algebra** —
this *is* the character type `(wordHopf α).Character R`, i.e. the
subtype of group-like (shuffle-multiplicative, normalized) signature
series. The monoid structure (tensor/Chen product) and, over a
commutative ring, the group structure (shuffle antipode inverse) come
from the abstract character theory of
`HopfAlgebras.Combinatorial.Basic`. -/
abbrev Signature (α : Type u) (R : Type v) [CommSemiring R] :
    Type (max u v) :=
  (wordHopf α).Character R

namespace Signature

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- The underlying series of the convolution unit is the unit series. -/
theorem one_val : ((1 : Signature α R) : (List α → R)) =
    Word.unit α R := by
  funext w
  cases w with
  | nil => rfl
  | cons c t => rfl

/-- The underlying series of a product is the tensor product. -/
theorem mul_val (σ τ : Signature α R) :
    ((σ * τ : Signature α R) : (List α → R)) =
      Word.tensorProduct σ.1 τ.1 :=
  rfl

/-- The coefficient of a word in a bundled signature. -/
def coeff (σ : Signature α R) (w : List α) : R :=
  Word.coeff σ.1 w

@[simp]
theorem coeff_apply (σ : Signature α R) (w : List α) :
    coeff σ w = σ.1 w :=
  rfl

@[simp]
theorem coeff_nil (σ : Signature α R) :
    coeff σ [] = 1 :=
  Word.IsGroupLike.coeff_nil σ.2

@[ext]
theorem ext {σ τ : Signature α R}
    (h : ∀ w, coeff σ w = coeff τ w) : σ = τ := by
  apply Subtype.ext
  funext w
  exact h w

/-- The identity signature. -/
def unit (α : Type u) (R : Type v) [CommSemiring R] : Signature α R :=
  ⟨Word.unit α R, Word.unit_isGroupLike⟩

/-- The identity signature is the convolution unit of the character
monoid. -/
theorem unit_eq_one : unit α R = (1 : Signature α R) :=
  Subtype.ext one_val.symm

@[simp]
theorem unit_coeff_nil :
    coeff (unit α R) [] = 1 :=
  rfl

@[simp]
theorem unit_coeff_cons (x : α) (w : List α) :
    coeff (unit α R) (x :: w) = 0 :=
  rfl

theorem shuffle (σ : Signature α R) (u v : List α) :
    coeff σ u * coeff σ v = Word.shuffleCoeff σ.1 u v :=
  Word.IsGroupLike.shuffle σ.2 u v

theorem satisfiesShuffleUpToDegree (σ : Signature α R) (n : Nat) :
    Word.SatisfiesShuffleUpToDegree σ.1 n :=
  Word.IsGroupLike.satisfiesShuffleUpToDegree σ.2 n

/-- Relabel a bundled signature by mapping letters. -/
def comapMapLetters {γ : Type u} {δ : Type z} (f : γ → δ)
    (σ : Signature δ R) : Signature γ R :=
  ⟨Word.comapMapLetters f σ.1, Word.IsGroupLike.comapMapLetters σ.2 f⟩

@[simp]
theorem coeff_comapMapLetters {γ : Type u} {δ : Type z}
    (f : γ → δ) (σ : Signature δ R) (w : List γ) :
    coeff (comapMapLetters f σ) w = coeff σ (w.map f) :=
  rfl

@[simp]
theorem comapMapLetters_id (σ : Signature α R) :
    comapMapLetters id σ = σ := by
  ext w
  simp [comapMapLetters, coeff]

theorem comapMapLetters_comp {γ : Type u} {δ : Type z} {ε : Type w}
    (f : γ → δ) (g : δ → ε) (σ : Signature ε R) :
    comapMapLetters f (comapMapLetters g σ) = comapMapLetters (g ∘ f) σ := by
  ext word
  simp [comapMapLetters, Word.comapMapLetters_comp, Function.comp_def]

@[simp]
theorem comapMapLetters_unit {γ : Type u} {δ : Type z} (f : γ → δ) :
    comapMapLetters f (unit δ R) = unit γ R := by
  ext word
  cases word <;> simp [comapMapLetters, unit]

end Signature

end RoughPaths
