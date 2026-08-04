import PassantCodeQ13.AssociationTransport.Base

/-! # The rho-ten square in the binary elliptic association algebra -/

namespace PassantCodeQ13.AssociationTransport

/-- Compact Boolean evaluation checks that the square of `A10` is `A12` entrywise. -/
theorem rhoTen_square_entry_certificate :
    booleanMatrixEqualityCheck
      (booleanParityProduct (relationBooleanMatrix 10) (relationBooleanMatrix 10))
      (relationBooleanMatrix 12) = true := by
  native_decide

/-- The relation matrices satisfy `A10² = A12`. -/
theorem rhoTen_square_parity_certificate :
    relationLinearMatrix 10 * relationLinearMatrix 10 = relationLinearMatrix 12 := by
  simp only [relationLinearMatrix]
  rw [← booleanParityProduct_linearize]
  exact congrArg booleanMatrix
    (booleanMatrixEqualityCheck_sound rhoTen_square_entry_certificate)

end PassantCodeQ13.AssociationTransport
