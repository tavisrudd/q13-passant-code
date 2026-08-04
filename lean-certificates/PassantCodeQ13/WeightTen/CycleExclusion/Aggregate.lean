import PassantCodeQ13.WeightTen.CycleExclusion.Residue0
import PassantCodeQ13.WeightTen.CycleExclusion.Residue1
import PassantCodeQ13.WeightTen.CycleExclusion.Residue2
import PassantCodeQ13.WeightTen.CycleExclusion.Residue3
import PassantCodeQ13.WeightTen.CycleExclusion.Residue4
import PassantCodeQ13.WeightTen.CycleExclusion.Residue5
import PassantCodeQ13.WeightTen.CycleExclusion.Residue6

/-!
# Exclusion of two-regular weight-ten configurations at the base point

The seven independently elaborated residue shards partition the unordered pairs of secant
neighbours of the normalized internal point `(1,0,2)` by the coordinate index of the lower endpoint
modulo seven.  Together they show that every configuration consisting of that point, one such pair,
and one point in each of the seven six-point passant fibres through it carries three points on some
passant or contains a point with three secant neighbours.

Neither may happen in a ten-point support of a codeword of the passant code all of whose points
have secant degree two: passant rows are parity checks, so every passant meets a support evenly,
and pencil parity at a support point bounds its secant degree by two.  The configuration shape
itself, and the transport of the fixed base point to an arbitrary internal point, are established
outside this module.
-/

namespace PassantCodeQ13.WeightTen.CycleExclusion

/-- Each residue shard of secant pairs passes the obstruction check. -/
theorem shardObstructed_of_lt_seven : ∀ residue, residue < 7 → shardObstructed residue = true := by
  intro residue residue_lt
  interval_cases residue
  · exact Residue0.shard_obstructed
  · exact Residue1.shard_obstructed
  · exact Residue2.shard_obstructed
  · exact Residue3.shard_obstructed
  · exact Residue4.shard_obstructed
  · exact Residue5.shard_obstructed
  · exact Residue6.shard_obstructed

/-- No configuration of the base point, an unordered pair of its secant neighbours, and one point in
each passant fibre through it avoids both obstructions. -/
theorem obstructed_of_base_pair_and_fibres
    {pair : List Nat} (pair_mem : pair ∈ secantNeighbors.sublistsLen 2)
    {path : List MarkedPoint} (selection : Selection markedFibres path) :
    obstructed (markedStart pair ++ path) = true :=
  obstructed_of_shards shardObstructed_of_lt_seven pair_mem selection

end PassantCodeQ13.WeightTen.CycleExclusion
