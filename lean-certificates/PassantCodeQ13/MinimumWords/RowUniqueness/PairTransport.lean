import PassantCodeQ13.MinimumWords.RowUniqueness.Base

/-!
# Indexed passant-join transport

The displayed-index Boolean test agrees with the semantic existence of a common passant line.
-/

namespace PassantCodeQ13.MinimumWords.RowUniqueness

/-- Indexed passant joins are exactly semantic passant joins. -/
theorem indexedPassantJoin_eq_true_iff
    (first second : RelativeConicArcs.PassantCodeQ13.InternalPoint) :
    indexedPassantJoin first second = true ↔
      RelativeConicArcs.PassantCodeQ13.HasPassantJoin first second := by
  native_decide +revert

end PassantCodeQ13.MinimumWords.RowUniqueness
