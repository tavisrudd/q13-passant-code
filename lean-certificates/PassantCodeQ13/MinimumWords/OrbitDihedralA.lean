import PassantCodeQ13.MinimumWords.Base

/-! # First minimum-word orbit with dihedral stabilizer

The displayed twelve-set is expanded under the normalized projective action and checked by native
evaluation.
-/

namespace PassantCodeQ13.MinimumWords

/-- The first dihedral representative has a 91-element kernel orbit of binary span rank 36. -/
theorem orbitDihedralA_certificate :
    (supportOrbit representativeDihedralA).length = 91 ∧
      orbitKernelCheck (supportOrbit representativeDihedralA) = true ∧
      binaryRank (supportOrbit representativeDihedralA) = 36 := by
  native_decide

end PassantCodeQ13.MinimumWords
