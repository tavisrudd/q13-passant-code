import PassantCodeQ13.MinimumWords.RowUniqueness.Base

namespace PassantCodeQ13.MinimumWords.RowUniqueness

/-- Triangle transport for first-point indices congruent to four modulo seven. -/
theorem row_extension_residue_four (firstIndex : Fin 78)
    (residue_eq : firstIndex.1 % 7 = 4) : rowExtensionCheckAt firstIndex = true := by
  native_decide +revert

end PassantCodeQ13.MinimumWords.RowUniqueness
