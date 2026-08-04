import PassantCodeQ13.AssociationTransport.Base

/-! # Association certificate for the second dihedral minimum-word orbit -/

namespace PassantCodeQ13.AssociationTransport

open PassantCodeQ13.MinimumWords

/-- Compact Boolean evaluation identifies the second dihedral orbit Gram matrix with `A12` and
checks its rows in `ker A0`, entrywise. -/
theorem orbitDihedralB_entry_certificate :
    let A0 := relationBooleanMatrix 0
    let A12 := relationBooleanMatrix 12
    let N := orbitSupportBooleanMatrix (supportOrbit representativeDihedralB)
    (booleanMatrixEqualityCheck (booleanParityProduct N.transpose N) A12 &&
      booleanMatrixEqualityCheck (booleanParityProduct A0 N.transpose) booleanZeroMatrix) = true := by
  native_decide

/-- The compact checks give Boolean orbit Gram and kernel equalities. -/
theorem orbitDihedralB_boolean_certificate :
    let A0 := relationBooleanMatrix 0
    let A12 := relationBooleanMatrix 12
    let N := orbitSupportBooleanMatrix (supportOrbit representativeDihedralB)
    booleanParityProduct N.transpose N = A12 ∧
      booleanParityProduct A0 N.transpose = booleanZeroMatrix := by
  dsimp only
  have checks := orbitDihedralB_entry_certificate
  simp only [Bool.and_eq_true] at checks
  exact ⟨booleanMatrixEqualityCheck_sound checks.1,
    booleanMatrixEqualityCheck_sound checks.2⟩

/-- The second dihedral orbit has Gram matrix `A12` and all its rows lie in `ker A0`. -/
theorem orbitDihedralB_Gram_and_kernel :
    let N := orbitSupportMatrix (supportOrbit representativeDihedralB)
    N.transpose * N = relationLinearMatrix 12 ∧ relationLinearMatrix 0 * N.transpose = 0 := by
  have certificate := orbitDihedralB_boolean_certificate
  dsimp only at certificate
  simp only [orbitSupportMatrix, relationLinearMatrix]
  constructor
  · rw [← booleanMatrix_transpose, ← booleanParityProduct_linearize]
    exact congrArg booleanMatrix certificate.1
  · rw [← booleanMatrix_transpose, ← booleanParityProduct_linearize, certificate.2,
      booleanMatrix_zero]

end PassantCodeQ13.AssociationTransport
