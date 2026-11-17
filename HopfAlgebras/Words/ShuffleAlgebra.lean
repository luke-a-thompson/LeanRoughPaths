import HopfAlgebras.Combinatorial.Shuffle
import HopfAlgebras.Util.DerivationArea
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel

/-!
# The shuffle algebra as a commutative ring

`ShuffleAlgebra R α` is the free `R`-module on words over `α` with the
shuffle product: the linear span of the basis of `wordHopf α`, as a
commutative `R`-algebra.

Deleting the last letter is a derivation, `ShuffleAlgebra.deletion`, with
values in `α →₀ ShuffleAlgebra R α` (one component per deleted letter).
Appending a letter inverts it, `ShuffleAlgebra.integral`. The right
half-shuffle `p ≺ q` and the signed area are then `∫ p dq` and
`∫ (p dq - q dp)` for this derivation.
-/

namespace HopfAlgebras

/-- Finite `R`-linear combinations of words, multiplied by shuffling. -/
def ShuffleAlgebra (R : Type*) (α : Type*) [CommRing R] : Type _ := List α →₀ R

namespace ShuffleAlgebra

variable {R : Type*} {α : Type*} [CommRing R]

noncomputable section

instance : AddCommGroup (ShuffleAlgebra R α) := inferInstanceAs (AddCommGroup (List α →₀ R))

instance : Module R (ShuffleAlgebra R α) := inferInstanceAs (Module R (List α →₀ R))

/-- A word, as a basis element. -/
def word (w : List α) : ShuffleAlgebra R α := Finsupp.single w (1 : R)

/-- Extend a function on words linearly. -/
def lift {V : Type*} [AddCommGroup V] [Module R V] (f : List α → V) :
    ShuffleAlgebra R α →ₗ[R] V := Finsupp.linearCombination R f

theorem single_eq_smul_word (w : List α) (c : R) :
    (Finsupp.single w c : ShuffleAlgebra R α) = c • word w :=
  (Finsupp.smul_single_one w c).symm

@[simp] theorem lift_word {V : Type*} [AddCommGroup V] [Module R V] (f : List α → V)
    (w : List α) : lift (R := R) f (word w) = f w := by
  show Finsupp.linearCombination R f (Finsupp.single w 1) = f w
  rw [Finsupp.linearCombination_single, one_smul]

@[ext] theorem linearMap_ext {V : Type*} [AddCommGroup V] [Module R V]
    {f g : ShuffleAlgebra R α →ₗ[R] V} (h : ∀ w, f (word w) = g (word w)) : f = g := by
  have key : ∀ (w : List α) (c : R), f (c • word w) = g (c • word w) := fun w c => by
    rw [map_smul, map_smul, h]
  exact Finsupp.lhom_ext fun w c => (congrArg f (single_eq_smul_word w c)).trans
    ((key w c).trans (congrArg g (single_eq_smul_word w c)).symm)

/-- Induction on the word basis and linear combinations. -/
@[elab_as_elim] theorem induction {P : ShuffleAlgebra R α → Prop}
    (zero : P 0) (word : ∀ w, P (word w)) (add : ∀ p q, P p → P q → P (p + q))
    (smul : ∀ (c : R) p, P p → P (c • p)) (p : ShuffleAlgebra R α) : P p := by
  induction p using Finsupp.induction_linear with
  | zero => exact zero
  | add p q hp hq => exact add p q hp hq
  | single w c =>
      rw [single_eq_smul_word]
      exact smul c _ (word w)

/-! ### The shuffle product -/

/-- The shuffle product, as a bilinear map. -/
def mulₗ : ShuffleAlgebra R α →ₗ[R] ShuffleAlgebra R α →ₗ[R] ShuffleAlgebra R α :=
  lift fun u => lift fun v => ((Word.shuffle u v).map word).sum

instance : Mul (ShuffleAlgebra R α) := ⟨fun p q => mulₗ p q⟩

instance : One (ShuffleAlgebra R α) := ⟨word []⟩

theorem mul_def (p q : ShuffleAlgebra R α) : p * q = mulₗ p q := rfl

theorem one_def : (1 : ShuffleAlgebra R α) = word [] := rfl

@[simp] theorem word_mul_word (u v : List α) :
    (word u : ShuffleAlgebra R α) * word v = ((Word.shuffle u v).map word).sum := by
  simp [mul_def, mulₗ]

private theorem mul_comm' (p q : ShuffleAlgebra R α) : p * q = q * p := by
  have h : mulₗ (R := R) (α := α) = LinearMap.flip mulₗ := by
    apply linearMap_ext; intro u
    apply linearMap_ext; intro v
    simpa [← mul_def] using ((Word.shuffle_comm_perm u v).map word).sum_eq
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

private theorem one_mul' (p : ShuffleAlgebra R α) : 1 * p = p := by
  have h : mulₗ (word ([] : List α) : ShuffleAlgebra R α) = LinearMap.id := by
    apply linearMap_ext; intro w
    simp [← mul_def]
  exact LinearMap.congr_fun h p

private theorem list_sum_mul (l : List (ShuffleAlgebra R α)) (a : ShuffleAlgebra R α) :
    l.sum * a = (l.map (· * a)).sum := by
  induction l with
  | nil => simp [mul_def]
  | cons x l ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
      exact LinearMap.map_add₂ mulₗ x l.sum a

private theorem mul_list_sum (a : ShuffleAlgebra R α) (l : List (ShuffleAlgebra R α)) :
    a * l.sum = (l.map (a * ·)).sum := by
  induction l with
  | nil => simp [mul_def]
  | cons x l ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
      exact map_add (mulₗ a) x l.sum

private theorem mul_assoc' (p q r : ShuffleAlgebra R α) : p * q * r = p * (q * r) := by
  have h : (mulₗ (R := R) (α := α)).compr₂ mulₗ =
      (LinearMap.llcomp R (ShuffleAlgebra R α) (ShuffleAlgebra R α)
        (ShuffleAlgebra R α)).compl₁₂ mulₗ mulₗ := by
    apply linearMap_ext; intro u
    apply linearMap_ext; intro v
    apply linearMap_ext; intro w
    change (word u : ShuffleAlgebra R α) * word v * word w = word u * (word v * word w)
    have hperm := ((Word.shuffle_flatMap_shuffle_perm u v w).map (word (R := R))).sum_eq
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def] at hperm
    rw [word_mul_word, word_mul_word, list_sum_mul, mul_list_sum, List.map_map, List.map_map]
    simpa only [Function.comp_def, word_mul_word] using hperm
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun h p) q) r

instance : CommRing (ShuffleAlgebra R α) :=
  { (inferInstance : AddCommGroup (ShuffleAlgebra R α)) with
    mul := (· * ·)
    one := 1
    left_distrib := fun p q r => map_add (mulₗ p) q r
    right_distrib := fun p q r => by simp [mul_def]
    zero_mul := fun p => by simp [mul_def]
    mul_zero := fun p => map_zero (mulₗ p)
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := fun p => by rw [mul_comm', one_mul']
    mul_comm := mul_comm' }

instance : Algebra R (ShuffleAlgebra R α) :=
  Algebra.ofModule (fun c p q => by simp [mul_def]) (fun c p q => by simp [mul_def])

/-! ### The constant coefficient -/

/-- The constant coefficient: the counit of the shuffle Hopf algebra. -/
def constant : ShuffleAlgebra R α →ₗ[R] R := lift fun w => if w.isEmpty then 1 else 0

@[simp] theorem constant_word (w : List α) :
    constant (word w : ShuffleAlgebra R α) = if w.isEmpty then 1 else 0 := lift_word _ _

@[simp] theorem constant_one : constant (1 : ShuffleAlgebra R α) = 1 := by simp [one_def]

theorem constant_mul (p q : ShuffleAlgebra R α) :
    constant (p * q) = constant p * constant q := by
  have h : (mulₗ (R := R) (α := α)).compr₂ constant =
      (LinearMap.mul R R).compl₁₂ constant constant := by
    apply linearMap_ext; intro u
    apply linearMap_ext; intro v
    simpa [← mul_def, map_list_sum, List.map_map, Function.comp_def, wordHopf] using
      (wordHopf α).mul_count_one (R := R) u v
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

/-! ### Deleting and appending the last letter -/

/-- Delete the last letter of each word, recording which letter it was. -/
def deletionₗ : ShuffleAlgebra R α →ₗ[R] (α →₀ ShuffleAlgebra R α) :=
  lift fun w => match w.reverse with
    | [] => 0
    | a :: vs => Finsupp.single a (word vs.reverse)

@[simp] theorem deletionₗ_word_nil :
    deletionₗ (word ([] : List α) : ShuffleAlgebra R α) = 0 := by simp [deletionₗ]

@[simp] theorem deletionₗ_word_append (w : List α) (a : α) :
    deletionₗ (word (w ++ [a]) : ShuffleAlgebra R α) = Finsupp.single a (word w) := by
  simp [deletionₗ]

private theorem single_list_sum (a : α) (l : List (ShuffleAlgebra R α)) :
    (Finsupp.single a l.sum : α →₀ ShuffleAlgebra R α) = (l.map (Finsupp.single a)).sum :=
  map_list_sum (Finsupp.singleAddHom a) l

private theorem deletionₗ_word_mul_word (u v : List α) :
    deletionₗ ((word u : ShuffleAlgebra R α) * word v) =
      (word u : ShuffleAlgebra R α) • deletionₗ (word v) +
        (word v : ShuffleAlgebra R α) • deletionₗ (word u) := by
  have h1 : deletionₗ (1 : ShuffleAlgebra R α) = 0 := deletionₗ_word_nil
  induction u using List.reverseRecOn with
  | nil => rw [← one_def, one_mul]; simp [h1]
  | append_singleton u a _ =>
    induction v using List.reverseRecOn with
    | nil => rw [← one_def, mul_one]; simp [h1]
    | append_singleton v b _ =>
      rw [word_mul_word, ((Word.shuffle_concat_concat_perm a b u v).map word).sum_eq,
        deletionₗ_word_append, deletionₗ_word_append, Finsupp.smul_single, Finsupp.smul_single,
        smul_eq_mul, smul_eq_mul, mul_comm (word (v ++ [b])) (word u), word_mul_word,
        word_mul_word, single_list_sum, single_list_sum]
      simp [map_list_sum, List.map_map, Function.comp_def, add_comm]

/-- **Deleting the last letter is a derivation of the shuffle product.** -/
def deletion : Derivation R (ShuffleAlgebra R α) (α →₀ ShuffleAlgebra R α) where
  toLinearMap := deletionₗ
  map_one_eq_zero' := deletionₗ_word_nil
  leibniz' p q := by
    induction p using induction with
    | zero => simp
    | word u =>
      induction q using induction with
      | zero => simp
      | word v => exact deletionₗ_word_mul_word u v
      | add q q' hq hq' => simp only [mul_add, map_add, hq, hq', smul_add, add_smul]; abel
      | smul c q hq => simp only [mul_smul_comm, map_smul, hq, smul_add, smul_assoc, smul_comm c]
    | add p p' hp hp' => simp only [add_mul, map_add, hp, hp', smul_add, add_smul]; abel
    | smul c p hp => simp only [smul_mul_assoc, map_smul, hp, smul_add, smul_assoc, smul_comm q c]

@[simp] theorem deletion_word_nil :
    deletion (word ([] : List α) : ShuffleAlgebra R α) = 0 := deletionₗ_word_nil

@[simp] theorem deletion_word_append (w : List α) (a : α) :
    deletion (word (w ++ [a]) : ShuffleAlgebra R α) = Finsupp.single a (word w) :=
  deletionₗ_word_append w a

/-- Append a letter to every word. -/
def append (a : α) : ShuffleAlgebra R α →ₗ[R] ShuffleAlgebra R α :=
  lift fun w => word (w ++ [a])

@[simp] theorem append_word (a : α) (w : List α) :
    append a (word w : ShuffleAlgebra R α) = word (w ++ [a]) := lift_word _ _

/-- Integration against the letters: the inverse of `deletion`. -/
def integral : (α →₀ ShuffleAlgebra R α) →ₗ[R] ShuffleAlgebra R α :=
  Finsupp.lsum R fun a => append a

@[simp] theorem integral_single (a : α) (p : ShuffleAlgebra R α) :
    integral (Finsupp.single a p) = append a p := by
  simp [integral]

theorem deletion_append (a : α) (p : ShuffleAlgebra R α) :
    deletion (append a p) = Finsupp.single a p := by
  induction p using induction with
  | zero => simp
  | word w => simp
  | add p q hp hq => simp only [map_add, hp, hq, Finsupp.single_add]
  | smul c p hp => rw [map_smul, Derivation.map_smul, hp, Finsupp.smul_single]

/-- Differentiating an integral returns the integrand. -/
@[simp] theorem deletion_integral (m : α →₀ ShuffleAlgebra R α) :
    deletion (integral m) = m := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m n hm hn => simp only [map_add, hm, hn]
  | single a p => rw [integral_single, deletion_append]

@[simp] theorem constant_append (a : α) (p : ShuffleAlgebra R α) :
    constant (append a p) = 0 := by
  induction p using induction with
  | zero => simp
  | word w => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | smul c p hp => simp only [map_smul, hp, smul_zero]

@[simp] theorem constant_integral (m : α →₀ ShuffleAlgebra R α) :
    constant (integral m) = 0 := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m n hm hn => simp only [map_add, hm, hn, add_zero]
  | single a p => rw [integral_single, constant_append]

/-- Integrating a differential recovers everything but the constant. -/
theorem integral_deletion (p : ShuffleAlgebra R α) :
    integral (deletion p) = p - constant p • 1 := by
  induction p using induction with
  | zero => simp
  | word w =>
    induction w using List.reverseRecOn with
    | nil => simp [one_def]
    | append_singleton w a _ => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_smul]; abel
  | smul c p hp =>
      rw [Derivation.map_smul, map_smul, hp, map_smul, smul_sub, smul_eq_mul, mul_smul]

/-! ### Half-shuffle and signed area -/

/-- The right half-shuffle `∫ p dq`: the last letter comes from `q`. -/
def halfShuffle (p q : ShuffleAlgebra R α) : ShuffleAlgebra R α :=
  integral (p • deletion q)

/-- The signed area `∫ (p dq - q dp)`. -/
def area (p q : ShuffleAlgebra R α) : ShuffleAlgebra R α :=
  integral (Derivation.area deletion p q)

theorem area_eq (p q : ShuffleAlgebra R α) : area p q = halfShuffle p q - halfShuffle q p := by
  simp [area, halfShuffle, Derivation.area]

@[simp] theorem deletion_halfShuffle (p q : ShuffleAlgebra R α) :
    deletion (halfShuffle p q) = p • deletion q := deletion_integral _

@[simp] theorem deletion_area (p q : ShuffleAlgebra R α) :
    deletion (area p q) = Derivation.area deletion p q := deletion_integral _

@[simp] theorem constant_halfShuffle (p q : ShuffleAlgebra R α) :
    constant (halfShuffle p q) = 0 := constant_integral _

@[simp] theorem constant_area (p q : ShuffleAlgebra R α) : constant (area p q) = 0 :=
  constant_integral _

/-- Words are iterated half-shuffles of their letters. -/
theorem halfShuffle_word_singleton (w : List α) (a : α) :
    halfShuffle (word w : ShuffleAlgebra R α) (word [a]) = word (w ++ [a]) := by
  have h : deletion (word [a] : ShuffleAlgebra R α) = Finsupp.single a 1 := by
    simpa [one_def] using deletion_word_append (R := R) [] a
  simp [halfShuffle, h, Finsupp.smul_single]

/-- The half-shuffle as a linear map in its first argument. -/
def halfShuffleRight (q : ShuffleAlgebra R α) : ShuffleAlgebra R α →ₗ[R] ShuffleAlgebra R α where
  toFun p := halfShuffle p q
  map_add' p p' := by simp [halfShuffle, add_smul]
  map_smul' c p := by simp [halfShuffle, smul_assoc]

@[simp] theorem halfShuffleRight_apply (p q : ShuffleAlgebra R α) :
    halfShuffleRight q p = halfShuffle p q := rfl

/-- Integration by parts: the shuffle product is the sum of the two
half-shuffles, up to constants. -/
theorem mul_eq_halfShuffle_add (p q : ShuffleAlgebra R α) :
    p * q = halfShuffle p q + halfShuffle q p + (constant p * constant q) • 1 := by
  have h := integral_deletion (p * q)
  rw [deletion.leibniz, map_add, constant_mul] at h
  rw [halfShuffle, halfShuffle, h]
  abel

end
end ShuffleAlgebra
end HopfAlgebras
