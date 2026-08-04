import PassantCodeQ13.AssociationTransport.Base

/-! # The rho-twelve square in the binary elliptic association algebra -/

namespace PassantCodeQ13.AssociationTransport

/-- Compact Boolean evaluation checks that the square of `A12` is `A9` entrywise. -/
theorem rhoTwelve_square_entry_certificate :
    booleanMatrixEqualityCheck
      (booleanParityProduct (relationBooleanMatrix 12) (relationBooleanMatrix 12))
      (relationBooleanMatrix 9) = true := by
  native_decide

/-- The relation matrices satisfy `A12² = A9`. -/
theorem rhoTwelve_square_parity_certificate :
    relationLinearMatrix 12 * relationLinearMatrix 12 = relationLinearMatrix 9 := by
  simp only [relationLinearMatrix]
  rw [← booleanParityProduct_linearize]
  exact congrArg booleanMatrix
    (booleanMatrixEqualityCheck_sound rhoTwelve_square_entry_certificate)

end PassantCodeQ13.AssociationTransport
