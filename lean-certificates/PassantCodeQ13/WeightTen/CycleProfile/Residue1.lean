import PassantCodeQ13.WeightTen.Base

/-! Finite leaf for cycle-profile secant pairs whose first normalized coordinate index
is congruent to 1 modulo seven.  Native evaluation checks the shard against the common 216-value
left syndrome image. -/

namespace PassantCodeQ13.WeightTen.CycleProfile

open PassantCodeQ13.WeightTen

/-- The cycle-profile residue-1 shard has no zero-syndrome support. -/
theorem residue1_syndrome_disjoint : cycleProfileCheck 1 = true := by
  native_decide

end PassantCodeQ13.WeightTen.CycleProfile
