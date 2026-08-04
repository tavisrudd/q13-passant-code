import PassantCodeQ13.WeightTen.PencilTransport

/-!
# The bits of an incidence syndrome

The weight-ten certificates store the passant rows through an internal point as the set bits of a
natural number, the incidence syndrome of that point.  Their obstruction predicates read those
syndromes bitwise: two points lie on no common passant exactly when the bitwise conjunction of
their syndromes vanishes, and three points lie on a common passant exactly when the conjunction of
their three syndromes does not.

This module proves those readings.  The syndrome is accumulated by a fold over the passant indices
below `78`, so its bit at an index is characterized by induction on the bound rather than by a
finite search, and the resulting characterization is transported to the incidence relation of
`RelativeConicArcs.PassantCodeQ13.Geometry` through the dictionary of
`PassantCodeQ13.WeightTen.PencilTransport`.
-/

namespace PassantCodeQ13.WeightTen.SyndromeBits

open RelativeConicArcs.PassantCodeQ13
open PassantCodeQ13.WeightTen
open PassantCodeQ13.WeightTen.PencilTransport

/-- The incidence syndrome of an internal point accumulated over the passant rows of index below a
bound. -/
def syndromeBelow (bound point : Nat) : Nat :=
  (List.range bound).foldl (fun syndrome line =>
    if incidentAt line point then syndrome ||| (1 <<< line) else syndrome) 0

/-- Raising the bound by one adds the row of that index when it is incident. -/
theorem syndromeBelow_succ (bound point : Nat) :
    syndromeBelow (bound + 1) point =
      if incidentAt bound point then syndromeBelow bound point ||| (1 <<< bound)
      else syndromeBelow bound point := by
  rw [syndromeBelow, List.range_succ, List.foldl_append]
  rfl

/-- A syndrome bit is set exactly at the incident rows below the bound. -/
theorem testBit_syndromeBelow (bound point line : Nat) :
    (syndromeBelow bound point).testBit line =
      (decide (line < bound) && incidentAt line point) := by
  induction bound with
  | zero => simp [syndromeBelow]
  | succ bound induction =>
      rw [syndromeBelow_succ]
      by_cases incident : incidentAt bound point = true
      · rw [if_pos incident, Nat.testBit_or, induction,
          show (1 <<< bound) = 2 ^ bound by simp [Nat.shiftLeft_eq],
          Nat.testBit_two_pow]
        rcases Nat.lt_trichotomy line bound with below | equal | above
        · have : line < bound + 1 := by omega
          simp [below, this, Nat.ne_of_gt below]
        · subst equal
          simp [incident]
        · have : ¬line < bound + 1 := by omega
          simp [Nat.not_lt_of_gt above, this, Nat.ne_of_lt above]
      · have not_incident : incidentAt bound point = false := by
          simpa using incident
        rw [if_neg incident, induction]
        rcases Nat.lt_trichotomy line bound with below | equal | above
        · have : line < bound + 1 := by omega
          simp [below, this]
        · subst equal
          simp [not_incident]
        · have : ¬line < bound + 1 := by omega
          simp [Nat.not_lt_of_gt above, this]

/-- The stored incidence syndrome is the fold over all `78` passant rows. -/
theorem columnSyndrome_eq_syndromeBelow (point : Nat) :
    columnSyndrome point = syndromeBelow 78 point := rfl

/-- A syndrome bit at a displayed passant index records incidence with that passant. -/
theorem testBit_columnSyndrome (point line : Fin 78) :
    (columnSyndrome point.1).testBit line.1 = true ↔
      Incident (passantLineAt line) (internalPointAt point) := by
  rw [columnSyndrome_eq_syndromeBelow, testBit_syndromeBelow]
  simp [line.2, incidentAt_iff line point]

/-- Beyond the displayed passant rows every syndrome bit is clear. -/
theorem testBit_columnSyndrome_of_ge {line : Nat} (bound : 78 ≤ line) (point : Nat) :
    (columnSyndrome point).testBit line = false := by
  rw [columnSyndrome_eq_syndromeBelow, testBit_syndromeBelow]
  simp [Nat.not_lt_of_ge bound]

/-- Vanishing bitwise conjunction of two incidence syndromes is absence of a common passant. -/
theorem and_columnSyndrome_eq_zero_iff (first second : Fin 78) :
    columnSyndrome first.1 &&& columnSyndrome second.1 = 0 ↔
      ¬WeightEight.PassantJoin (internalPointAt first) (internalPointAt second) := by
  constructor
  · rintro vanishing ⟨line, first_incident, second_incident⟩
    obtain ⟨index, rfl⟩ := passantLineAt_bijective.surjective line
    have bit : (columnSyndrome first.1 &&& columnSyndrome second.1).testBit index.1 = true := by
      rw [Nat.testBit_and, (testBit_columnSyndrome first index).mpr first_incident,
        (testBit_columnSyndrome second index).mpr second_incident]
      rfl
    rw [vanishing] at bit
    simp at bit
  · intro disjoint
    apply Nat.eq_of_testBit_eq
    intro line
    rw [Nat.testBit_and]
    simp only [Nat.zero_testBit]
    by_cases bound : line < 78
    · by_cases first_bit : (columnSyndrome first.1).testBit line = true
      · by_cases second_bit : (columnSyndrome second.1).testBit line = true
        · exact absurd ⟨passantLineAt ⟨line, bound⟩,
            (testBit_columnSyndrome first ⟨line, bound⟩).mp first_bit,
            (testBit_columnSyndrome second ⟨line, bound⟩).mp second_bit⟩ disjoint
        · simp [Bool.eq_false_iff.mpr second_bit]
      · simp [Bool.eq_false_iff.mpr first_bit]
    · simp [testBit_columnSyndrome_of_ge (Nat.le_of_not_lt bound)]

/-- Nonvanishing bitwise conjunction of three incidence syndromes is a common passant. -/
theorem and_columnSyndrome_ne_zero_iff (first second third : Fin 78) :
    columnSyndrome first.1 &&& columnSyndrome second.1 &&& columnSyndrome third.1 ≠ 0 ↔
      ∃ line : PassantLine, Incident line (internalPointAt first) ∧
        Incident line (internalPointAt second) ∧ Incident line (internalPointAt third) := by
  constructor
  · intro nonvanishing
    by_contra absent
    apply nonvanishing
    apply Nat.eq_of_testBit_eq
    intro line
    rw [Nat.testBit_and, Nat.testBit_and]
    simp only [Nat.zero_testBit]
    by_cases bound : line < 78
    · by_cases first_bit : (columnSyndrome first.1).testBit line = true
      · by_cases second_bit : (columnSyndrome second.1).testBit line = true
        · by_cases third_bit : (columnSyndrome third.1).testBit line = true
          · exact absurd ⟨passantLineAt ⟨line, bound⟩,
              (testBit_columnSyndrome first ⟨line, bound⟩).mp first_bit,
              (testBit_columnSyndrome second ⟨line, bound⟩).mp second_bit,
              (testBit_columnSyndrome third ⟨line, bound⟩).mp third_bit⟩ absent
          · simp [Bool.eq_false_iff.mpr third_bit]
        · simp [Bool.eq_false_iff.mpr second_bit]
      · simp [Bool.eq_false_iff.mpr first_bit]
    · simp [testBit_columnSyndrome_of_ge (Nat.le_of_not_lt bound)]
  · rintro ⟨line, first_incident, second_incident, third_incident⟩ vanishing
    obtain ⟨index, rfl⟩ := passantLineAt_bijective.surjective line
    have bit : (columnSyndrome first.1 &&& columnSyndrome second.1 &&&
        columnSyndrome third.1).testBit index.1 = true := by
      rw [Nat.testBit_and, Nat.testBit_and,
        (testBit_columnSyndrome first index).mpr first_incident,
        (testBit_columnSyndrome second index).mpr second_incident,
        (testBit_columnSyndrome third index).mpr third_incident]
      rfl
    rw [vanishing] at bit
    simp at bit

end PassantCodeQ13.WeightTen.SyndromeBits
