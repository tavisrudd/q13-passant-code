import PassantCodeQ13.MinimumWords.RowUniqueness.Base

namespace PassantCodeQ13.MinimumWords.RowUniqueness

/-- Every geometric passant row has zero triple concurrence in the decoded minimum layer. -/
theorem geometric_rows_have_zero_triple_concurrence :
    GeometricRowsHaveZeroTripleConcurrence := by
  unfold GeometricRowsHaveZeroTripleConcurrence
  native_decide +revert

end PassantCodeQ13.MinimumWords.RowUniqueness
