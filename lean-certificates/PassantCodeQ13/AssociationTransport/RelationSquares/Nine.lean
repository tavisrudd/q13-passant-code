import PassantCodeQ13.AssociationTransport.Base

/-! # The rho-nine square in the binary elliptic association algebra -/

namespace PassantCodeQ13.AssociationTransport

/-- Compact Boolean evaluation checks that the square of `A9` is `A10` entrywise. -/
theorem rhoNine_square_entry_certificate :
    booleanMatrixEqualityCheck
      (booleanParityProduct (relationBooleanMatrix 9) (relationBooleanMatrix 9))
      (relationBooleanMatrix 10) = true := by
  native_decide

/-- The relation matrices satisfy `A9² = A10`. -/
theorem rhoNine_square_parity_certificate :
    relationLinearMatrix 9 * relationLinearMatrix 9 = relationLinearMatrix 10 := by
  simp only [relationLinearMatrix]
  rw [← booleanParityProduct_linearize]
  exact congrArg booleanMatrix
    (booleanMatrixEqualityCheck_sound rhoNine_square_entry_certificate)

end PassantCodeQ13.AssociationTransport
