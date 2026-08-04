import RelativeConicArcs.PassantCodeQ13.Geometry

/-!
# Executable q=13 weight-ten syndrome semantics

The internal points and passant lines are taken from the normalized coordinate lists in
`RelativeConicArcs.PassantCodeQ13.Geometry`.  A syndrome is a 78-bit natural number whose set bits
are the incident passant rows.  XOR is therefore addition of incidence columns over `ZMod 2`.

At the fixed internal point `(1,0,2)`, the other coordinates split into seven passant fibres of six
points and thirty-five secant-join neighbors.  The two weight-ten parity profiles are checked by
meet-in-the-middle syndrome disjointness.  This file contains definitions only; native terminals
are split across leaf modules.
-/

namespace PassantCodeQ13.WeightTen

open RelativeConicArcs.PassantCodeQ13

/-- The normalized internal coordinate at a bounded integer index. -/
def internalAt (index : Nat) : Triple :=
  internalCoordinateList.getD index verticalTriple

/-- The normalized passant coordinate at a bounded integer index. -/
def passantAt (index : Nat) : Triple :=
  passantCoordinateList.getD index verticalTriple

/-- Executable incidence for the indexed normalized coordinate lists. -/
def incidentAt (line point : Nat) : Bool :=
  let l := passantAt line
  let p := internalAt point
  l.x * p.x + l.y * p.y + l.z * p.z == 0

/-- The 78-bit incidence syndrome of one internal point. -/
def columnSyndrome (point : Nat) : Nat :=
  (List.range 78).foldl (fun syndrome line =>
    if incidentAt line point then syndrome ||| (1 <<< line) else syndrome) 0

/-- XOR of the incidence columns at the listed point indices. -/
def xorColumns (points : List Nat) : Nat :=
  points.foldl (fun syndrome point => syndrome ^^^ columnSyndrome point) 0

/-- The seven passant rows through the base point `(1,0,2)`, whose index is zero. -/
def linesThroughBase : List Nat :=
  (List.range 78).filter fun line => incidentAt line 0

/-- The six other internal points on each passant through the base point. -/
def fibres : List (List Nat) :=
  linesThroughBase.map fun line =>
    (List.range 78).filter fun point => point != 0 && incidentAt line point

/-- Internal points whose join with the base point is secant. -/
def secantNeighbors : List Nat :=
  (List.range 78).filter fun point =>
    point != 0 && !(fibres.flatten.contains point)

/-- Cartesian choices of one element from each list. -/
def choices : List (List Nat) → List (List Nat)
  | [] => [[]]
  | options :: remaining =>
      options.flatMap fun option => (choices remaining).map fun tail => option :: tail

/-- The syndrome image of a Cartesian product of point lists. -/
def productSyndromes (pointLists : List (List Nat)) : List Nat :=
  (choices pointLists).map xorColumns |>.eraseDups

/-- Fibre indices other than the distinguished fibre. -/
def remainingFibres (special : Nat) : List Nat :=
  (List.range 7).filter fun index => index != special

/-- Incidence-column syndromes offered by one list of point indices. -/
def columnOptions (points : List Nat) : List Nat :=
  points.map columnSyndrome

/-- The three ordinary-fibre increment lists on the left of the isolated meet-in-the-middle
decomposition. -/
def isolatedLeftOptions (special : Nat) : List (List Nat) :=
  (remainingFibres special).take 3 |>.map fun index =>
    columnOptions (fibres.getD index [])

/-- The base column, the twenty three-point increments in the distinguished fibre, and the three
ordinary-fibre increment lists on the right of the isolated meet-in-the-middle decomposition. -/
def isolatedRightOptions (special : Nat) : List (List Nat) :=
  let remaining := remainingFibres special
  [[columnSyndrome 0], (fibres.getD special []).sublistsLen 3 |>.map xorColumns] ++
    (remaining.drop 3 |>.map fun index => columnOptions (fibres.getD index []))

/-- The seven ordinary-fibre increment lists in the cycle profile. -/
def cycleFibreOptions : List (List Nat) :=
  fibres.map columnOptions

/-- The 216 left syndromes for the isolated profile with a distinguished fibre. -/
def isolatedLeft (special : Nat) : List Nat :=
  productSyndromes ((remainingFibres special).take 3 |>.map fun index => fibres.getD index [])

/-- The 4320 right syndromes for the isolated profile with a distinguished fibre. -/
def isolatedRight (special : Nat) : List Nat :=
  let remaining := remainingFibres special
  let triples := (fibres.getD special []).sublistsLen 3
  let tails := choices (remaining.drop 3 |>.map fun index => fibres.getD index [])
  (triples.flatMap fun triple => tails.map fun tail =>
    columnSyndrome 0 ^^^ xorColumns triple ^^^ xorColumns tail).eraseDups

/-- Whether the two syndrome images for one isolated profile are disjoint. -/
def isolatedProfileCheck (special : Nat) : Bool :=
  let left := isolatedLeft special
  (isolatedRight special).all fun syndrome => !left.contains syndrome

/-- The common 216 left syndromes for the cycle profile. -/
def cycleLeft : List Nat :=
  productSyndromes (fibres.take 3)

/-- Secant-neighbor pairs assigned to one of seven coordinate-residue shards. -/
def cyclePairs (residue : Nat) : List (List Nat) :=
  (secantNeighbors.sublistsLen 2).filter fun pair =>
    match pair with
    | first :: _ => first % 7 == residue
    | _ => false

/-- The right syndrome image for one cycle-profile residue shard. -/
def cycleRight (residue : Nat) : List Nat :=
  let baseSyndrome := columnSyndrome 0
  let tailSyndromes := (choices (fibres.drop 3)).map xorColumns
  let pairSyndromes := (cyclePairs residue).map xorColumns
  tailSyndromes.flatMap fun tail => pairSyndromes.map fun pair =>
    baseSyndrome ^^^ tail ^^^ pair

/-- Whether one cycle-profile shard is disjoint from the common left syndrome image. -/
def cycleProfileCheck (residue : Nat) : Bool :=
  cycleRight residue |>.all fun syndrome => !cycleLeft.contains syndrome

/-- The local conic partition has the required `7 × 6 + 35` shape. -/
def localPartitionCheck : Bool :=
  internalAt 0 == affineTriple 0 2 &&
    linesThroughBase.length == 7 &&
    fibres.all (fun fibre => fibre.length == 6) &&
    secantNeighbors.length == 35

end PassantCodeQ13.WeightTen
