import PassantCodeQ13.AssociationTransport.Base

/-! # Association certificate for the third dihedral minimum-word orbit -/

namespace PassantCodeQ13.AssociationTransport

open PassantCodeQ13.MinimumWords

/-- Compact Boolean evaluation identifies the third dihedral orbit Gram matrix with `A10` and
checks its rows in `ker A0`, entrywise. -/
theorem orbitDihedralC_entry_certificate :
    let A0 := relationBooleanMatrix 0
    let A10 := relationBooleanMatrix 10
    let N := orbitSupportBooleanMatrix (supportOrbit representativeDihedralC)
    (booleanMatrixEqualityCheck (booleanParityProduct N.transpose N) A10 &&
      booleanMatrixEqualityCheck (booleanParityProduct A0 N.transpose) booleanZeroMatrix) = true := by
  native_decide

/-- The compact checks give Boolean orbit Gram and kernel equalities. -/
theorem orbitDihedralC_boolean_certificate :
    let A0 := relationBooleanMatrix 0
    let A10 := relationBooleanMatrix 10
    let N := orbitSupportBooleanMatrix (supportOrbit representativeDihedralC)
    booleanParityProduct N.transpose N = A10 ∧
      booleanParityProduct A0 N.transpose = booleanZeroMatrix := by
  dsimp only
  have checks := orbitDihedralC_entry_certificate
  simp only [Bool.and_eq_true] at checks
  exact ⟨booleanMatrixEqualityCheck_sound checks.1,
    booleanMatrixEqualityCheck_sound checks.2⟩

/-- The third dihedral orbit has Gram matrix `A10` and all its rows lie in `ker A0`. -/
theorem orbitDihedralC_Gram_and_kernel :
    let N := orbitSupportMatrix (supportOrbit representativeDihedralC)
    N.transpose * N = relationLinearMatrix 10 ∧ relationLinearMatrix 0 * N.transpose = 0 := by
  have certificate := orbitDihedralC_boolean_certificate
  dsimp only at certificate
  simp only [orbitSupportMatrix, relationLinearMatrix]
  constructor
  · rw [← booleanMatrix_transpose, ← booleanParityProduct_linearize]
    exact congrArg booleanMatrix certificate.1
  · rw [← booleanMatrix_transpose, ← booleanParityProduct_linearize, certificate.2,
      booleanMatrix_zero]

end PassantCodeQ13.AssociationTransport
