import PassantCodeQ13.WeightTen.Base

/-! Finite leaf for cycle-profile secant pairs whose first normalized coordinate index
is congruent to 5 modulo seven.  Native evaluation checks the shard against the common 216-value
left syndrome image. -/

namespace PassantCodeQ13.WeightTen.CycleProfile

open PassantCodeQ13.WeightTen

/-- The cycle-profile residue-5 shard has no zero-syndrome support. -/
theorem residue5_syndrome_disjoint : cycleProfileCheck 5 = true := by
  native_decide

end PassantCodeQ13.WeightTen.CycleProfile
