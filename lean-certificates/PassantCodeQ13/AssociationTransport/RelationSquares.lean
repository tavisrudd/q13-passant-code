import PassantCodeQ13.AssociationTransport.RelationSquares.RhoZero
import PassantCodeQ13.AssociationTransport.RelationSquares.Nine
import PassantCodeQ13.AssociationTransport.RelationSquares.Ten
import PassantCodeQ13.AssociationTransport.RelationSquares.Twelve

/-! # Squaring identities in the binary elliptic association algebra -/

namespace PassantCodeQ13.AssociationTransport

/-- The executable association identities hold as matrix identities over the binary field. -/
theorem relation_matrix_identities :
    relationLinearMatrix 0 * relationLinearMatrix 0 =
        1 + relationLinearMatrix 9 + relationLinearMatrix 10 + relationLinearMatrix 12 ∧
      relationLinearMatrix 9 * relationLinearMatrix 9 = relationLinearMatrix 10 ∧
      relationLinearMatrix 10 * relationLinearMatrix 10 = relationLinearMatrix 12 ∧
      relationLinearMatrix 12 * relationLinearMatrix 12 = relationLinearMatrix 9 := by
  exact ⟨rhoZero_square_parity_certificate, rhoNine_square_parity_certificate,
    rhoTen_square_parity_certificate, rhoTwelve_square_parity_certificate⟩

end PassantCodeQ13.AssociationTransport
