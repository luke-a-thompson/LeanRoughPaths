import RoughPaths.Signature.Polynomial
import HopfAlgebras.Words.AreaReduction

open HopfAlgebras.Word HopfAlgebras.Word.Polynomial

-- The sign convention is fixed by the chronological two-letter identity.
example {α : Type*} (a b : α) :
    (2 : ℚ) • word [a, b] = shuffle (word [a]) (word [b]) + area (word [a]) (word [b]) := by
  have hab : halfShuffle (word [a]) (word [b]) = word [a, b] := by
    simpa using halfShuffle_word_append [a] [] b
  have hba : halfShuffle (word [b]) (word [a]) = word [b, a] := by
    simpa using halfShuffle_word_append [b] [] a
  rw [shuffle_eq_halfShuffle]
  simp only [area, hab, hba, constant_word, List.cons_ne_self, reduceIte,
    mul_zero, zero_smul, add_zero]
  module

-- Multiplicity is retained for a repeated letter.
example {α : Type*} (a : α) : shuffle (word [a]) (word [a]) = (2 : ℚ) • word [a, a] := by
  simp [shuffle_word, two_smul]

example {α : Type*} (a b c : α) : word [a,b,c] ∈ areaSpan ({a} + {b} + {c}) := by
  exact word_generated [a,b,c]

example {α : Type*} : word [] ∈ areaSpan (0 : Multiset α) := word_generated []

#print axioms HopfAlgebras.Word.Polynomial.word_generated
#print axioms RoughPaths.Signature.ext_of_area_eq
#print axioms RoughPaths.Signature.eq_of_area_eq_weight
#print axioms RoughPaths.Signature.derivative_pairing_area
#print axioms HopfAlgebras.Word.AreaReduction.diff_primitive
