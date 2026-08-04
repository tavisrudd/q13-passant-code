import PassantCodeQ13.Automorphisms.Base

/-!
# Regular projective orbit of the first three anchors

Native evaluation checks that the 2184 normalized invertible matrices act bijectively on the 78
internal coordinates, preserve the polar relation, and carry the first three anchors onto exactly
the ordered triples with relation pattern `(10,3,9)`.  The orbit has 2184 distinct elements, so
this is the regular triple orbit used by the automorphism argument.
-/

namespace PassantCodeQ13.Automorphisms

open PassantCodeQ13.AssociationAlgebra

/-- The first three displayed anchors have relation pattern `(10,3,9)`. -/
theorem anchorTriplePattern :
    rhoAt (anchors 0) (anchors 1) = 10 ∧ rhoAt (anchors 0) (anchors 2) = 3 ∧
      rhoAt (anchors 1) (anchors 2) = 9 := by
  native_decide

/-- The normalized projective matrix list has the order of `PGL(2,13)`. -/
theorem projectiveMatrices_length :
    PassantCodeQ13.MinimumWords.projectiveMatrices.length = 2184 := by
  native_decide

/-- Every normalized symmetric-square matrix action is a permutation of the internal points. -/
theorem matrixAction_bijective (matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length) :
    Function.Bijective (matrixAction matrix) := by
  native_decide +revert

/-- Every normalized symmetric-square matrix action preserves the polar relation. -/
theorem matrixAction_preservesRho
    (matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length) :
    PreservesRho (matrixAction matrix) := by
  unfold PreservesRho
  native_decide +revert

/-- The projective images of the first three anchors are exactly the triples of pattern
`(10,3,9)`, and all 2184 images are distinct. -/
theorem projectiveAnchorTriples_eq_patterned :
    projectiveAnchorTriples = patternedTriples ∧ projectiveAnchorTriples.card = 2184 := by
  native_decide

end PassantCodeQ13.Automorphisms
