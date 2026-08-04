import PassantCodeQ13.MinimumWords.RowUniqueness.Base

namespace PassantCodeQ13.MinimumWords.RowUniqueness

/-- Triangle transport for first-point indices congruent to five modulo seven. -/
theorem row_extension_residue_five (firstIndex : Fin 78)
    (residue_eq : firstIndex.1 % 7 = 5) : rowExtensionCheckAt firstIndex = true := by
  native_decide +revert

end PassantCodeQ13.MinimumWords.RowUniqueness
