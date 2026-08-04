import PassantCodeQ13.AssociationTransport.Base

/-! # The rho-zero square in the binary elliptic association algebra -/

namespace PassantCodeQ13.AssociationTransport

/-- Compact Boolean evaluation checks the rho-zero square identity entrywise. -/
theorem rhoZero_square_entry_certificate :
    booleanMatrixEqualityCheck
      (booleanParityProduct (relationBooleanMatrix 0) (relationBooleanMatrix 0))
      (booleanXorMatrix booleanIdentityMatrix
        (booleanXorMatrix (relationBooleanMatrix 9)
          (booleanXorMatrix (relationBooleanMatrix 10) (relationBooleanMatrix 12)))) = true := by
  native_decide

/-- The rho-zero relation matrix satisfies its binary square identity. -/
theorem rhoZero_square_parity_certificate :
    relationLinearMatrix 0 * relationLinearMatrix 0 =
      1 + relationLinearMatrix 9 + relationLinearMatrix 10 + relationLinearMatrix 12 := by
  have entries := booleanMatrixEqualityCheck_sound rhoZero_square_entry_certificate
  simp only [relationLinearMatrix]
  rw [← booleanParityProduct_linearize]
  rw [entries, booleanMatrix_xor, booleanMatrix_identity, booleanMatrix_xor, booleanMatrix_xor]
  simp only [add_assoc]

end PassantCodeQ13.AssociationTransport
