import PassantCodeQ13.MinimumWords.Base

/-! # The minimum-word orbit with symmetric-group stabilizer

Native evaluation expands the displayed twelve-set under all normalized elements of `PGL(2,13)`.
It checks 91 distinct kernel supports and binary span rank 36.
-/

namespace PassantCodeQ13.MinimumWords

/-- The symmetric-stabilizer representative has a 91-element orbit of weight-twelve codewords. -/
theorem orbitS4_size_and_kernel :
    (supportOrbit representativeS4).length = 91 ∧
      orbitKernelCheck (supportOrbit representativeS4) = true := by
  native_decide

/-- The symmetric-stabilizer orbit spans a 36-dimensional binary space. -/
theorem orbitS4_rank : binaryRank (supportOrbit representativeS4) = 36 := by
  native_decide

end PassantCodeQ13.MinimumWords
