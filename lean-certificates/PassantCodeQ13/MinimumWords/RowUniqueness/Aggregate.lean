import PassantCodeQ13.MinimumWords.RowUniqueness.ResidueZero
import PassantCodeQ13.MinimumWords.RowUniqueness.ResidueOne
import PassantCodeQ13.MinimumWords.RowUniqueness.ResidueTwo
import PassantCodeQ13.MinimumWords.RowUniqueness.ResidueThree
import PassantCodeQ13.MinimumWords.RowUniqueness.ResidueFour
import PassantCodeQ13.MinimumWords.RowUniqueness.ResidueFive
import PassantCodeQ13.MinimumWords.RowUniqueness.ResidueSix
import PassantCodeQ13.MinimumWords.RowUniqueness.PairTransport
import PassantCodeQ13.MinimumWords.RowUniqueness.ConcurrenceTransport

/-!
# Complete indexed triangle transport

The seven residue certificates cover every displayed internal-point index.  This module combines
them without further native evaluation.
-/

namespace PassantCodeQ13.MinimumWords.RowUniqueness

/-- Every indexed first point passes the exhaustive local-extension check. -/
theorem row_extension_check_all_indices (firstIndex : Fin 78) :
    rowExtensionCheckAt firstIndex = true := by
  have residue_lt : firstIndex.1 % 7 < 7 := Nat.mod_lt _ (by decide)
  interval_cases residue_eq : firstIndex.1 % 7
  · exact row_extension_residue_zero firstIndex residue_eq
  · exact row_extension_residue_one firstIndex residue_eq
  · exact row_extension_residue_two firstIndex residue_eq
  · exact row_extension_residue_three firstIndex residue_eq
  · exact row_extension_residue_four firstIndex residue_eq
  · exact row_extension_residue_five firstIndex residue_eq
  · exact row_extension_residue_six firstIndex residue_eq

/-- Every distinct displayed seed passes the exhaustive extension check; internally the seed is
sorted so the finite leaves evaluate each unordered triple only once. -/
theorem seed_extension_check_all_indices
    (firstIndex secondIndex thirdIndex : Fin 78)
    (indices_distinct : firstIndex ≠ secondIndex ∧ firstIndex ≠ thirdIndex ∧
      secondIndex ≠ thirdIndex)
    (seed_candidate : reconstructionCandidateCheck
      (indexedSeed firstIndex secondIndex thirdIndex) = true) :
    seedExtensionCheck firstIndex secondIndex thirdIndex = true := by
  have first_ne_second : firstIndex.1 ≠ secondIndex.1 :=
    fun equality => indices_distinct.1 (Fin.ext equality)
  have first_ne_third : firstIndex.1 ≠ thirdIndex.1 :=
    fun equality => indices_distinct.2.1 (Fin.ext equality)
  have second_ne_third : secondIndex.1 ≠ thirdIndex.1 :=
    fun equality => indices_distinct.2.2 (Fin.ext equality)
  have transport_sorted (sortedFirst sortedSecond sortedThird : Fin 78)
      (sorted_distinct : sortedFirst ≠ sortedSecond ∧ sortedFirst ≠ sortedThird ∧
        sortedSecond ≠ sortedThird)
      (first_lt_second : sortedFirst.1 < sortedSecond.1)
      (second_lt_third : sortedSecond.1 < sortedThird.1)
      (seed_eq : indexedSeed firstIndex secondIndex thirdIndex =
        indexedSeed sortedFirst sortedSecond sortedThird) :
      seedExtensionCheck firstIndex secondIndex thirdIndex = true := by
    have sorted_candidate : reconstructionCandidateCheck
        (indexedSeed sortedFirst sortedSecond sortedThird) = true := by
      rw [← seed_eq]
      exact seed_candidate
    rw [seedExtensionCheck_eq_of_seed_eq firstIndex secondIndex thirdIndex
      sortedFirst sortedSecond sortedThird seed_eq]
    exact seedExtensionCheck_of_rowExtensionCheckAt sortedFirst sortedSecond sortedThird
      sorted_distinct first_lt_second second_lt_third sorted_candidate
        (row_extension_check_all_indices sortedFirst)
  rcases Nat.lt_or_gt_of_ne first_ne_second with first_lt_second | second_lt_first
  · rcases Nat.lt_or_gt_of_ne second_ne_third with second_lt_third | third_lt_second
    · apply transport_sorted firstIndex secondIndex thirdIndex indices_distinct
        first_lt_second second_lt_third rfl
    · rcases Nat.lt_or_gt_of_ne first_ne_third with first_lt_third | third_lt_first
      · apply transport_sorted firstIndex thirdIndex secondIndex
          ⟨indices_distinct.2.1, indices_distinct.1, indices_distinct.2.2.symm⟩
          first_lt_third third_lt_second
        ext point
        simp [indexedSeed, or_comm, or_left_comm, or_assoc]
      · apply transport_sorted thirdIndex firstIndex secondIndex
          ⟨indices_distinct.2.1.symm, indices_distinct.2.2.symm, indices_distinct.1⟩
          third_lt_first first_lt_second
        ext point
        simp [indexedSeed, or_comm, or_left_comm, or_assoc]
  · rcases Nat.lt_or_gt_of_ne first_ne_third with first_lt_third | third_lt_first
    · apply transport_sorted secondIndex firstIndex thirdIndex
        ⟨indices_distinct.1.symm, indices_distinct.2.2, indices_distinct.2.1⟩
        second_lt_first first_lt_third
      ext point
      simp [indexedSeed, or_comm, or_left_comm, or_assoc]
    · rcases Nat.lt_or_gt_of_ne second_ne_third with second_lt_third | third_lt_second
      · apply transport_sorted secondIndex thirdIndex firstIndex
          ⟨indices_distinct.2.2, indices_distinct.1.symm, indices_distinct.2.1.symm⟩
          second_lt_third third_lt_first
        ext point
        simp [indexedSeed, or_comm, or_left_comm, or_assoc]
      · apply transport_sorted thirdIndex secondIndex firstIndex
          ⟨indices_distinct.2.2.symm, indices_distinct.2.1.symm, indices_distinct.1.symm⟩
          third_lt_second second_lt_first
        ext point
        simp [indexedSeed, or_comm, or_left_comm, or_assoc]

end PassantCodeQ13.MinimumWords.RowUniqueness
