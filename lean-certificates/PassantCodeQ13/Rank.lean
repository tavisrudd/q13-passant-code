import PassantCodeQ13.MinimumWords.Base

/-!
# Exact binary elimination of the q=13 incidence rows

The 78 passant rows are encoded directly from the normalized conic incidence relation.  The
descending-pivot evaluator in `PassantCodeQ13.MinimumWords.Base` performs exact Gaussian
elimination over the binary field.  Kernel reduction checks rank 42.

The shared semantic theorem uses `Module.finrank`.  A separate symbolic correctness theorem for
the bit-row evaluator is required to transport this leaf to
`RelativeConicArcs.PassantCodeQ13.IncidenceMapHasRankFortyTwo`.
-/

namespace PassantCodeQ13.Rank

open PassantCodeQ13.WeightTen
open PassantCodeQ13.MinimumWords

/-- The 78 binary passant rows as 78-bit natural numbers. -/
def incidenceRows : List Nat :=
  (List.range 78).map fun line =>
    (List.range 78).foldl (fun row point =>
      if incidentAt line point then row ||| (1 <<< point) else row) 0

/-- Exact binary elimination gives incidence-row rank 42. -/
theorem incidenceRows_rank : binaryRank incidenceRows = 42 := by
  decide +kernel

end PassantCodeQ13.Rank
