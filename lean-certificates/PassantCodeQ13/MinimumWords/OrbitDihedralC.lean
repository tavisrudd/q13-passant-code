import PassantCodeQ13.MinimumWords.Base

/-! # Third minimum-word orbit with dihedral stabilizer

The displayed twelve-set is expanded under the normalized projective action and checked by native
evaluation.
-/

namespace PassantCodeQ13.MinimumWords

/-- The third dihedral representative has a 91-element kernel orbit of binary span rank 36. -/
theorem orbitDihedralC_certificate :
    (supportOrbit representativeDihedralC).length = 91 ∧
      orbitKernelCheck (supportOrbit representativeDihedralC) = true ∧
      binaryRank (supportOrbit representativeDihedralC) = 36 := by
  native_decide

end PassantCodeQ13.MinimumWords
