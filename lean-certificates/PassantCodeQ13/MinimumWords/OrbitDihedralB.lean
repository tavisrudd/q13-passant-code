import PassantCodeQ13.MinimumWords.Base

/-! # Second minimum-word orbit with dihedral stabilizer

The displayed twelve-set is expanded under the normalized projective action and checked by native
evaluation.
-/

namespace PassantCodeQ13.MinimumWords

/-- The second dihedral representative has a 91-element kernel orbit of binary span rank 36. -/
theorem orbitDihedralB_certificate :
    (supportOrbit representativeDihedralB).length = 91 ∧
      orbitKernelCheck (supportOrbit representativeDihedralB) = true ∧
      binaryRank (supportOrbit representativeDihedralB) = 36 := by
  native_decide

end PassantCodeQ13.MinimumWords
