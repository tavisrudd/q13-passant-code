import PassantCodeQ13.MinimumWords.Reconstruction
import Batteries.Data.HashMap.Basic

/-!
# Fixed-point exhaustion of the weight-twelve supports

Fix the internal point with displayed index zero.  Row parity splits the other eleven points of a
weight-twelve codeword among the seven passant fibres and the secant neighbors of the fixed point.
There are four possible multiplicity types:

* one fibre of size five and six singleton fibres;
* two fibres of size three and five singleton fibres;
* one fibre of size three, six singleton fibres, and two secant neighbors;
* seven singleton fibres and four secant neighbors.

The definitions below exhaust these four domains by a syndrome-indexed meet in the middle.  Native
evaluation then identifies the resulting 56 kernel supports with the four disjoint 14-element
slices, through the fixed point, of the displayed projective orbits.  Thus the finite terminal is a
fixed-point exhaustion rather than a second enumeration of all 364 supports.
-/

namespace PassantCodeQ13.MinimumWords

open PassantCodeQ13.WeightTen

/-- Encode a list of internal-point indices as a 78-bit support. -/
def encodeIndices (points : List Nat) : Nat :=
  points.foldl (fun support point => support ||| (1 <<< point)) 0

/-- The 78 incidence columns, evaluated once for the fixed-point meet in the middle. -/
def cachedColumnSyndromes : Array Nat :=
  ((List.range 78).map columnSyndrome).toArray

/-- XOR of cached incidence columns at the listed point indices. -/
def xorCachedColumns (points : List Nat) : Nat :=
  points.foldl (fun syndrome point => syndrome ^^^ cachedColumnSyndromes.getD point 0) 0

/-- Insert a partial support into the bucket indexed by its incidence syndrome. -/
def insertSyndromeBucket (buckets : Std.HashMap Nat (List (List Nat)))
    (points : List Nat) : Std.HashMap Nat (List (List Nat)) :=
  let syndrome := xorCachedColumns points
  buckets.insert syndrome (points :: buckets[syndrome]?.getD [])

/-- Join two families of partial supports whose syndromes sum to the base-point syndrome. -/
def matchingBaseSupports (left right : List (List Nat)) : List Nat :=
  let buckets := left.foldl insertSyndromeBucket {}
  right.flatMap fun rightPoints =>
    let target := cachedColumnSyndromes.getD 0 0 ^^^ xorCachedColumns rightPoints
    (buckets[target]?.getD []).filterMap fun leftPoints =>
      let points := leftPoints ++ rightPoints
      if points.eraseDups.length = 11 then
        some (encodeIndices (0 :: points))
      else none

/-- Candidate supports with fibre pattern `(5,1,1,1,1,1,1;0)`. -/
def fiveOneFibreSolutions : List Nat :=
  (List.range 7).flatMap fun special =>
    let remaining := remainingFibres special
    let left := (fibres.getD special []).sublistsLen 5 |>.flatMap fun five =>
      (choices ((remaining.take 3).map fun index => fibres.getD index [])).map fun head =>
        five ++ head
    let right := choices ((remaining.drop 3).map fun index => fibres.getD index [])
    matchingBaseSupports left right

/-- Candidate supports with fibre pattern `(3,3,1,1,1,1,1;0)`. -/
def twoTripleFibreSolutions : List Nat :=
  ((List.range 7).sublistsLen 2).flatMap fun specialPair =>
    match specialPair with
    | [first, second] =>
        let remaining := (List.range 7).filter fun index => index != first && index != second
        let left := (fibres.getD first []).sublistsLen 3 |>.flatMap fun firstTriple =>
          (choices ((remaining.take 2).map fun index => fibres.getD index [])).map fun head =>
            firstTriple ++ head
        let right := (fibres.getD second []).sublistsLen 3 |>.flatMap fun secondTriple =>
          (choices ((remaining.drop 2).map fun index => fibres.getD index [])).map fun tail =>
            secondTriple ++ tail
        matchingBaseSupports left right
    | _ => []

/-- Candidate supports with fibre/secant pattern `(3,1,1,1,1,1,1;2)`. -/
def oneTripleTwoSecantSolutions : List Nat :=
  (List.range 7).flatMap fun special =>
    let remaining := remainingFibres special
    let left := (fibres.getD special []).sublistsLen 3 |>.flatMap fun triple =>
      (choices ((remaining.take 3).map fun index => fibres.getD index [])).map fun head =>
        triple ++ head
    let right := (choices ((remaining.drop 3).map fun index => fibres.getD index [])).flatMap
      fun tail => (secantNeighbors.sublistsLen 2).map fun pair => tail ++ pair
    matchingBaseSupports left right

/-- Candidate supports with fibre/secant pattern `(1,1,1,1,1,1,1;4)`. -/
def fourSecantSolutions : List Nat :=
  let left := (choices (fibres.take 3)).flatMap fun head =>
    (secantNeighbors.sublistsLen 2).map fun pair => head ++ pair
  let right := (choices (fibres.drop 3)).flatMap fun tail =>
    (secantNeighbors.sublistsLen 2).map fun pair => tail ++ pair
  matchingBaseSupports left right

/-- All weight-twelve kernel supports found by the four exhaustive fixed-point profiles. -/
def fixedPointWeightTwelveSolutions : List Nat :=
  (fiveOneFibreSolutions ++ twoTripleFibreSolutions ++ oneTripleTwoSecantSolutions ++
    fourSecantSolutions).eraseDups

/-- The four displayed projective orbits, restricted to supports containing the fixed point. -/
def fixedPointOrbitSlices : List Nat :=
  minimumSupportCodes.filter fun support => support.testBit 0

/-- The 28 projective transformations fixing the normalized internal point of index zero. -/
def fixedPointStabilizer : List Matrix2 :=
  projectiveMatrices.filter fun matrix =>
    internalIndex (act matrix (internalAt 0)) == 0

/-- Image of an encoded support under the symmetric-square projective action. -/
def actOnSupportCode (matrix : Matrix2) (support : Nat) : Nat :=
  (List.range 78).foldl (fun image point =>
    if support.testBit point then
      image ||| (1 <<< internalIndex (act matrix (internalAt point)))
    else image) 0

/-- Orbit of one encoded support under the fixed-point stabilizer. -/
def fixedPointStabilizerOrbit (support : Nat) : List Nat :=
  (fixedPointStabilizer.map fun matrix => actOnSupportCode matrix support).eraseDups

/-- The four fixed-point profile searches return exactly the 56 supports in the four orbit slices. -/
theorem fixedPoint_weightTwelve_exhaustion :
    fixedPointWeightTwelveSolutions.toFinset = fixedPointOrbitSlices.toFinset ∧
      fixedPointWeightTwelveSolutions.length = 56 ∧
      (supportOrbit representativeS4).countP (fun support => support.testBit 0) = 14 ∧
      (supportOrbit representativeDihedralA).countP (fun support => support.testBit 0) = 14 ∧
      (supportOrbit representativeDihedralB).countP (fun support => support.testBit 0) = 14 ∧
      (supportOrbit representativeDihedralC).countP (fun support => support.testBit 0) = 14 := by
  native_decide

/-- The order-28 fixed-point stabilizer acts transitively on each 14-support orbit slice. -/
theorem fixedPoint_slices_are_stabilizer_orbits :
    fixedPointStabilizer.length = 28 ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeS4)).toFinset =
        ((supportOrbit representativeS4).filter fun support => support.testBit 0).toFinset ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeDihedralA)).toFinset =
        ((supportOrbit representativeDihedralA).filter fun support => support.testBit 0).toFinset ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeDihedralB)).toFinset =
        ((supportOrbit representativeDihedralB).filter fun support => support.testBit 0).toFinset ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeDihedralC)).toFinset =
        ((supportOrbit representativeDihedralC).filter fun support => support.testBit 0).toFinset := by
  native_decide

end PassantCodeQ13.MinimumWords
