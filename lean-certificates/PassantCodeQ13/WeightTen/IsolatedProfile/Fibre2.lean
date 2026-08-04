import PassantCodeQ13.WeightTen.Base

/-! Finite leaf for the isolated weight-ten profile whose three-point passant fibre has
index 2 in the normalized list.  Native evaluation checks disjointness of all 216 left and 4320
right syndrome values. -/

namespace PassantCodeQ13.WeightTen.IsolatedProfile

open PassantCodeQ13.WeightTen

/-- The isolated profile with distinguished fibre 2 has no zero-syndrome support. -/
theorem fibre2_syndrome_disjoint : isolatedProfileCheck 2 = true := by
  native_decide

end PassantCodeQ13.WeightTen.IsolatedProfile
