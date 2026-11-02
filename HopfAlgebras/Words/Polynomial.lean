import HopfAlgebras.Words.Shuffle
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Algebra.Bilinear

/-! # Finite rational word polynomials

The shuffle product retains multiplicities, including for repeated letters.
-/

namespace HopfAlgebras.Word

abbrev Polynomial (α : Type*) := List α →₀ ℚ

namespace Polynomial

variable {α : Type*}
noncomputable section

/-- The polynomial consisting of one word. -/
def word (w : List α) : Polynomial α := Finsupp.single w 1

/-- Extend a function on words linearly. -/
def lift {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f : List α → V) : Polynomial α →ₗ[ℚ] V := Finsupp.linearCombination ℚ f

@[simp] theorem lift_word {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f : List α → V) (w : List α) : lift f (word w) = f w := by
  simp [lift, word]

/-- Bilinear extension of an operation on words. -/
def lift₂ (f : List α → List α → Polynomial α) :
    Polynomial α →ₗ[ℚ] Polynomial α →ₗ[ℚ] Polynomial α :=
  lift (fun u => lift (f u))

@[simp] theorem lift₂_word (f : List α → List α → Polynomial α) (u v : List α) :
    lift₂ f (word u) (word v) = f u v := by simp [lift₂]

/-- Shuffle multiplication of word polynomials. -/
def shuffle : Polynomial α →ₗ[ℚ] Polynomial α →ₗ[ℚ] Polynomial α :=
  lift₂ (fun u v => ((Word.shuffle u v).map word).sum)

@[simp] theorem shuffle_word (u v : List α) :
    shuffle (word u) (word v) = ((Word.shuffle u v).map word).sum := by
  simp [shuffle]

/-- Appending a letter, extended linearly. -/
def append (a : α) : Polynomial α →ₗ[ℚ] Polynomial α := lift (fun w => word (w ++ [a]))

@[simp] theorem append_word (a : α) (w : List α) :
    append a (word w) = word (w ++ [a]) := lift_word _ _

/-- Right half-shuffle: the last letter comes from the second argument.
It is zero when that argument is empty. -/
def halfShuffle : Polynomial α →ₗ[ℚ] Polynomial α →ₗ[ℚ] Polynomial α :=
  lift₂ (fun u v => match v.reverse with
    | [] => 0
    | a :: vs => append a (shuffle (word u) (word vs.reverse)))

@[simp] theorem halfShuffle_word_nil (u : List α) :
    halfShuffle (word u) (word []) = 0 := by simp [halfShuffle]

@[simp] theorem halfShuffle_word_append (u v : List α) (a : α) :
    halfShuffle (word u) (word (v ++ [a])) = append a (shuffle (word u) (word v)) := by
  simp [halfShuffle]

/-- Signed area, with the convention `∫ u dv − v du`. -/
def area (p q : Polynomial α) : Polynomial α := halfShuffle p q - halfShuffle q p

@[simp] theorem area_self (p : Polynomial α) : area p p = 0 := sub_self _

theorem area_swap (p q : Polynomial α) : area p q = -area q p := by
  simp [area, neg_sub]

@[ext] theorem linearMap_ext {V : Type*} [AddCommGroup V] [Module ℚ V]
    {f g : Polynomial α →ₗ[ℚ] V} (h : ∀ w, f (word w) = g (word w)) : f = g := by
  apply Finsupp.lhom_ext
  intro w c
  have hc : Finsupp.single w c = c • word w := by simp [word]
  rw [hc, map_smul, map_smul, h]

theorem shuffle_comm (p q : Polynomial α) : shuffle p q = shuffle q p := by
  have h : shuffle (α := α) = LinearMap.flip shuffle := by
    apply linearMap_ext
    intro u
    apply linearMap_ext
    intro v
    simpa using ((Word.shuffle_comm_perm u v).map word).sum_eq
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

@[simp] theorem shuffle_one_left (p : Polynomial α) : shuffle (word []) p = p := by
  have h : shuffle (word ([] : List α)) = LinearMap.id := by
    apply linearMap_ext
    intro w
    simp
  exact LinearMap.congr_fun h p

@[simp] theorem shuffle_one_right (p : Polynomial α) : shuffle p (word []) = p := by
  rw [shuffle_comm, shuffle_one_left]

/-- Induction on the word basis and linear combinations. -/
@[elab_as_elim] theorem induction {P : Polynomial α → Prop}
    (zero : P 0) (word : ∀ w, P (Polynomial.word w))
    (add : ∀ p q, P p → P q → P (p + q))
    (smul : ∀ (c : ℚ) p, P p → P (c • p)) (p : Polynomial α) : P p := by
  induction p using Finsupp.induction_linear with
  | zero => exact zero
  | add p q hp hq => exact add p q hp hq
  | single w c =>
      have h : Finsupp.single w c = c • Polynomial.word w := by simp [Polynomial.word]
      rw [h]
      exact smul c _ (word w)

@[simp] theorem sum_apply {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (fs : List (V →ₗ[ℚ] W)) (v : V) :
    fs.sum v = (fs.map fun f => f v).sum := by
  exact map_list_sum (LinearMap.applyₗ (R := ℚ) v) fs

theorem shuffle_assoc (p q r : Polynomial α) :
    shuffle (shuffle p q) r = shuffle p (shuffle q r) := by
  have h : (shuffle (α := α)).compr₂ shuffle =
      (LinearMap.llcomp ℚ (Polynomial α) (Polynomial α) (Polynomial α)).compl₁₂ shuffle shuffle := by
    ext u v w : 6
    change shuffle (shuffle (word u) (word v)) (word w) =
      shuffle (word u) (shuffle (word v) (word w))
    simpa [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def, map_list_sum] using ((Word.shuffle_flatMap_shuffle_perm u v w).map word).sum_eq
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun h p) q) r

theorem halfShuffle_append (p q : Polynomial α) (a : α) :
    halfShuffle p (append a q) = append a (shuffle p q) := by
  have h : halfShuffle.compl₂ (append a) = shuffle.compr₂ (append a) := by
    apply linearMap_ext; intro u
    apply linearMap_ext; intro v
    simp
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

@[simp] theorem halfShuffle_one_right (p : Polynomial α) :
    halfShuffle p (word []) = 0 := by
  induction p using induction <;> simp_all

/-- The right Zinbiel identity. -/
theorem halfShuffle_assoc (p q r : Polynomial α) :
    halfShuffle p (halfShuffle q r) = halfShuffle (shuffle p q) r := by
  induction r using induction with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul c p hp => simp only [map_smul, hp]
  | word w =>
    induction w using List.reverseRecOn with
    | nil => simp
    | append_singleton w a _ =>
      rw [← append_word, halfShuffle_append, halfShuffle_append,
        halfShuffle_append, shuffle_assoc]

/-- Constant coefficient. -/
def constant : Polynomial α →ₗ[ℚ] ℚ := Finsupp.lapply []

@[simp] theorem constant_word (w : List α) :
    constant (word w) = if w = [] then 1 else 0 := by
  classical
  simp [constant, word, Finsupp.single_apply]

theorem halfShuffle_one_left (p : Polynomial α) :
    halfShuffle (word []) p = p - constant p • word [] := by
  induction p using induction with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_smul]; abel
  | smul c p hp => simp only [map_smul, hp, smul_sub, smul_smul]; rfl
  | word w =>
    induction w using List.reverseRecOn with
    | nil => simp
    | append_singleton w a _ => simp

theorem shuffle_eq_halfShuffle (p q : Polynomial α) :
    shuffle p q = halfShuffle p q + halfShuffle q p +
      (constant p * constant q) • word [] := by
  have h : shuffle (α := α) = halfShuffle + halfShuffle.flip +
      ((LinearMap.mul ℚ ℚ).compl₁₂ constant constant).compr₂
        (LinearMap.toSpanSingleton ℚ (Polynomial α) (word [])) := by
    apply linearMap_ext; intro u
    apply linearMap_ext; intro v
    change shuffle (word u) (word v) = halfShuffle (word u) (word v) +
      halfShuffle (word v) (word u) + (constant (word u) * constant (word v)) • word []
    induction u using List.reverseRecOn with
    | nil => simp [halfShuffle_one_left]
    | append_singleton u a _ =>
      induction v using List.reverseRecOn with
      | nil => simp
      | append_singleton v b _ =>
        have h := ((Word.shuffle_concat_concat_perm a b u v).map word).sum_eq
        simp only [halfShuffle_word_append]
        rw [shuffle_comm (word (v ++ [b])) (word u)]
        simpa [map_list_sum, List.map_map, Function.comp_def, add_comm] using h
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

@[simp] theorem constant_append (a : α) (p : Polynomial α) : constant (append a p) = 0 := by
  induction p using induction <;> simp_all

@[simp] theorem constant_halfShuffle (p q : Polynomial α) : constant (halfShuffle p q) = 0 := by
  induction q using induction with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | smul c p hp => simp only [map_smul, hp, smul_zero]
  | word w =>
    induction w using List.reverseRecOn with
    | nil => simp
    | append_singleton w a _ => rw [← append_word, halfShuffle_append]; simp

@[simp] theorem constant_area (p q : Polynomial α) : constant (area p q) = 0 := by
  simp [area]

/-- Integration of a product in the second argument (the product rule). -/
theorem halfShuffle_shuffle (p q r : Polynomial α) :
    halfShuffle p (shuffle q r) =
      halfShuffle (shuffle p q) r + halfShuffle (shuffle p r) q := by
  conv_lhs => rw [shuffle_eq_halfShuffle]
  simp only [map_add, map_smul, halfShuffle_one_right, smul_zero, add_zero,
    halfShuffle_assoc]

end
end Polynomial
end HopfAlgebras.Word
