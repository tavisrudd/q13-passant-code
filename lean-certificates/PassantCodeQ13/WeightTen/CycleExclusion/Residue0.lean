import PassantCodeQ13.WeightTen.CycleExclusion

/-!
# Obstruction check for one residue class of secant pairs

Kernel reduction checks that every configuration formed by the base point `(1,0,2)`, one unordered
pair of its secant neighbours whose lower endpoint has coordinate index congruent to 0 modulo
seven, and one point in each of the seven passant fibres through the base point has a passant
carrying three of its points or a point with three secant neighbours inside it.
-/

namespace PassantCodeQ13.WeightTen.CycleExclusion.Residue0

open PassantCodeQ13.WeightTen.CycleExclusion

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Every configuration over this residue shard of secant pairs is obstructed. -/
theorem shard_obstructed : shardObstructed 0 = true := by
  decide +kernel

end PassantCodeQ13.WeightTen.CycleExclusion.Residue0
