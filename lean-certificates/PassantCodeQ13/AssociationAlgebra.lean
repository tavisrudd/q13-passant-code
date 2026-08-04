import PassantCodeQ13.MinimumWords.Base
import RelativeConicArcs.PassantCodeQ13.AssociationAlgebra

/-!
# Binary elliptic association-algebra leaves over `ZMod 13`

The six elliptic relations are computed from the normalized polar invariant on the 78 internal
coordinates.  Their binary adjacency rows are encoded as natural-number bit sets.  Native
evaluation checks the four identities used to explain the span of the minimum-word orbits and the
exact ranks of the four relevant relation matrices.
-/

namespace PassantCodeQ13.AssociationAlgebra

open RelativeConicArcs.PassantCodeQ13
open PassantCodeQ13.WeightTen
open PassantCodeQ13.MinimumWords

/-- Polar invariant of two indexed internal coordinates. -/
def rhoAt (first second : Nat) : Field13 :=
  let u := internalAt first
  let v := internalAt second
  polarValue u v ^ 2 * (pointDiscriminant u * pointDiscriminant v)⁻¹

/-- One binary row of an off-diagonal elliptic relation. -/
def relationRow (value : Field13) (first : Nat) : Nat :=
  (List.range 78).foldl (fun row second =>
    if first != second && rhoAt first second == value then row ||| (1 <<< second) else row) 0

/-- The 78 rows of one elliptic relation matrix. -/
def relationMatrix (value : Field13) : List Nat :=
  (List.range 78).map (relationRow value)

/-- Product of two binary matrices represented by row bit sets. -/
def matrixProduct (left right : List Nat) : List Nat :=
  (List.range 78).map fun row =>
    (List.range 78).foldl (fun answer column =>
      let parity := (List.range 78).foldl (fun bit middle =>
        if (left.getD row 0).testBit middle && (right.getD middle 0).testBit column
          then !bit else bit) false
      if parity then answer ||| (1 <<< column) else answer) 0

/-- The binary identity matrix as row bit sets. -/
def identityMatrix : List Nat :=
  (List.range 78).map fun index => 1 <<< index

/-- Pointwise XOR of four binary row matrices. -/
def xorFour (first second third fourth : List Nat) : List Nat :=
  List.zipWith (fun a rest => a ^^^ rest)
    first (List.zipWith (fun b rest => b ^^^ rest)
      second (List.zipWith (fun c d => c ^^^ d) third fourth))

/-- The four relation matrices have ranks `42,36,36,36`. -/
theorem relation_matrix_ranks :
    binaryRank (relationMatrix 0) = 42 ∧
      binaryRank (relationMatrix 9) = 36 ∧
      binaryRank (relationMatrix 10) = 36 ∧
      binaryRank (relationMatrix 12) = 36 := by
  native_decide

/-- The square of the rho-zero relation is `I + A9 + A10 + A12` over the binary field. -/
theorem rhoZero_square :
    matrixProduct (relationMatrix 0) (relationMatrix 0) =
      xorFour identityMatrix (relationMatrix 9) (relationMatrix 10) (relationMatrix 12) := by
  native_decide

/-- The three rank-36 relation matrices form a squaring cycle over the binary field. -/
theorem rankThirtySix_squaring_cycle :
    matrixProduct (relationMatrix 9) (relationMatrix 9) = relationMatrix 10 ∧
      matrixProduct (relationMatrix 10) (relationMatrix 10) = relationMatrix 12 ∧
      matrixProduct (relationMatrix 12) (relationMatrix 12) = relationMatrix 9 := by
  native_decide

end PassantCodeQ13.AssociationAlgebra
