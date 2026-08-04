import PassantCodeQ13.AssociationTransport.Base

/-! # Association certificate for the symmetric-stabilizer minimum-word orbit -/

namespace PassantCodeQ13.AssociationTransport

open PassantCodeQ13.MinimumWords

/-- Compact Boolean evaluation identifies the orbit Gram matrix with `A9` and checks its rows in
`ker A0`, entrywise. -/
theorem orbitS4_entry_certificate :
    let A0 := relationBooleanMatrix 0
    let A9 := relationBooleanMatrix 9
    let N := orbitSupportBooleanMatrix (supportOrbit representativeS4)
    (booleanMatrixEqualityCheck (booleanParityProduct N.transpose N) A9 &&
      booleanMatrixEqualityCheck (booleanParityProduct A0 N.transpose) booleanZeroMatrix) = true := by
  native_decide

/-- The compact checks give Boolean orbit Gram and kernel equalities. -/
theorem orbitS4_boolean_certificate :
    let A0 := relationBooleanMatrix 0
    let A9 := relationBooleanMatrix 9
    let N := orbitSupportBooleanMatrix (supportOrbit representativeS4)
    booleanParityProduct N.transpose N = A9 ∧
      booleanParityProduct A0 N.transpose = booleanZeroMatrix := by
  dsimp only
  have checks := orbitS4_entry_certificate
  simp only [Bool.and_eq_true] at checks
  exact ⟨booleanMatrixEqualityCheck_sound checks.1,
    booleanMatrixEqualityCheck_sound checks.2⟩

/-- The symmetric-stabilizer orbit has Gram matrix `A9` and all its rows lie in `ker A0`. -/
theorem orbitS4_Gram_and_kernel :
    let N := orbitSupportMatrix (supportOrbit representativeS4)
    N.transpose * N = relationLinearMatrix 9 ∧ relationLinearMatrix 0 * N.transpose = 0 := by
  have certificate := orbitS4_boolean_certificate
  dsimp only at certificate
  simp only [orbitSupportMatrix, relationLinearMatrix]
  constructor
  · rw [← booleanMatrix_transpose, ← booleanParityProduct_linearize]
    exact congrArg booleanMatrix certificate.1
  · rw [← booleanMatrix_transpose, ← booleanParityProduct_linearize, certificate.2,
      booleanMatrix_zero]

end PassantCodeQ13.AssociationTransport
