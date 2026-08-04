import PassantCodeQ13.WeightTen.Base

/-!
# Projective orbits of displayed weight-twelve supports

This module implements the symmetric-square action of `PGL(2,13)` on the normalized internal-point
list.  Supports are encoded as 78-bit natural numbers.  The four displayed representatives are
expanded under all 2184 normalized projective matrices; leaf modules check their orbit sizes,
kernel syndromes, disjointness, and binary span ranks.
-/

namespace PassantCodeQ13.MinimumWords

open RelativeConicArcs.PassantCodeQ13
open PassantCodeQ13.WeightTen

/-- A normalized representative of a projective two-by-two matrix. -/
structure Matrix2 where
  a : Field13
  b : Field13
  c : Field13
  d : Field13
deriving DecidableEq, Repr

/-- Determinant of a two-by-two matrix. -/
def determinant (matrix : Matrix2) : Field13 :=
  matrix.a * matrix.d - matrix.b * matrix.c

/-- The normalized invertible projective matrices, one representative per element of `PGL(2,13)`. -/
def projectiveMatrices : List Matrix2 :=
  let field := fieldElements
  let first := field.flatMap fun b => field.flatMap fun c =>
    field.map fun d => (⟨1, b, c, d⟩ : Matrix2)
  let second := field.flatMap fun c => field.map fun d => (⟨0, 1, c, d⟩ : Matrix2)
  let third := field.map fun d => (⟨0, 0, 1, d⟩ : Matrix2)
  (first ++ second ++ third ++ [(⟨0, 0, 0, 1⟩ : Matrix2)]).filter fun matrix =>
    determinant matrix != 0

/-- Normalize a nonzero homogeneous triple by its first nonzero coordinate. -/
def normalizeTriple (point : Triple) : Triple :=
  if point.x != 0 then
    ⟨1, point.y * point.x⁻¹, point.z * point.x⁻¹⟩
  else if point.y != 0 then
    ⟨0, 1, point.z * point.y⁻¹⟩
  else verticalTriple

/-- Symmetric-square action of a projective matrix on a ternary quadratic coefficient triple. -/
def act (matrix : Matrix2) (point : Triple) : Triple :=
  normalizeTriple ⟨
    matrix.a ^ 2 * point.x + 2 * matrix.a * matrix.b * point.y + matrix.b ^ 2 * point.z,
    matrix.a * matrix.c * point.x +
      (matrix.a * matrix.d + matrix.b * matrix.c) * point.y +
      matrix.b * matrix.d * point.z,
    matrix.c ^ 2 * point.x + 2 * matrix.c * matrix.d * point.y + matrix.d ^ 2 * point.z⟩

/-- Index of a normalized internal coordinate; 78 denotes a failed lookup. -/
def internalIndex (point : Triple) : Nat :=
  internalCoordinateList.idxOf point

/-- Encode a displayed coordinate support as a 78-bit natural number. -/
def encodeSupport (support : List Triple) : Nat :=
  support.foldl (fun answer point => answer ||| (1 <<< internalIndex point)) 0

/-- Orbit of a displayed support under the normalized projective matrices. -/
def supportOrbit (support : List Triple) : List Nat :=
  (projectiveMatrices.map fun matrix =>
    encodeSupport (support.map (act matrix))).eraseDups

/-- Reduce a binary row against a descending-pivot basis. -/
def reduceRow (basis : List Nat) (row : Nat) : Nat :=
  basis.foldl (fun value pivot =>
    if value.testBit (Nat.log2 pivot) then value ^^^ pivot else value) row

/-- Insert a binary row into a descending-pivot echelon basis. -/
def insertRow (basis : List Nat) (row : Nat) : List Nat :=
  let reduced := reduceRow basis row
  if reduced = 0 then basis else basis ++ [reduced]

/-- Binary rank of a list of 78-bit support rows. -/
def binaryRank (rows : List Nat) : Nat :=
  (rows.foldl insertRow []).length

/-- First displayed orbit representative, with stabilizer isomorphic to `S4`. -/
def representativeS4 : List Triple := [
  ⟨1, 0, 2⟩, ⟨1, 0, 5⟩, ⟨1, 1, 3⟩, ⟨1, 1, 6⟩,
  ⟨1, 2, 9⟩, ⟨1, 3, 4⟩, ⟨1, 3, 7⟩, ⟨1, 6, 5⟩,
  ⟨1, 8, 7⟩, ⟨1, 11, 2⟩, ⟨1, 11, 12⟩, ⟨1, 12, 6⟩]

/-- First displayed orbit representative with a dihedral stabilizer of order 24. -/
def representativeDihedralA : List Triple := [
  ⟨1, 0, 2⟩, ⟨1, 0, 5⟩, ⟨1, 1, 3⟩, ⟨1, 1, 6⟩,
  ⟨1, 2, 12⟩, ⟨1, 5, 5⟩, ⟨1, 6, 2⟩, ⟨1, 6, 4⟩,
  ⟨1, 8, 4⟩, ⟨1, 8, 6⟩, ⟨1, 9, 9⟩, ⟨1, 12, 9⟩]

/-- Second displayed orbit representative with a dihedral stabilizer of order 24. -/
def representativeDihedralB : List Triple := [
  ⟨1, 0, 2⟩, ⟨1, 3, 2⟩, ⟨1, 4, 5⟩, ⟨1, 1, 8⟩,
  ⟨1, 4, 8⟩, ⟨1, 1, 7⟩, ⟨1, 7, 12⟩, ⟨1, 3, 3⟩,
  ⟨1, 9, 11⟩, ⟨1, 10, 11⟩, ⟨1, 0, 5⟩, ⟨1, 8, 7⟩]

/-- Third displayed orbit representative with a dihedral stabilizer of order 24. -/
def representativeDihedralC : List Triple := [
  ⟨1, 0, 2⟩, ⟨1, 0, 7⟩, ⟨1, 1, 6⟩, ⟨1, 2, 11⟩,
  ⟨1, 3, 7⟩, ⟨1, 3, 11⟩, ⟨1, 5, 1⟩, ⟨1, 5, 10⟩,
  ⟨1, 6, 4⟩, ⟨1, 7, 2⟩, ⟨1, 8, 1⟩, ⟨1, 8, 6⟩]

/-- Executable check that every support in an orbit has twelve coordinates and zero syndrome. -/
def orbitKernelCheck (orbit : List Nat) : Bool :=
  orbit.all fun support =>
    ((List.range 78).filter support.testBit).length == 12 &&
    (List.range 78).foldl (fun syndrome point =>
      if support.testBit point then syndrome ^^^ columnSyndrome point else syndrome) 0 == 0

end PassantCodeQ13.MinimumWords
