import PassantCodeQ13.AssociationAlgebra

/-!
# Four-anchor data for the elliptic relation scheme

The 78 indexed internal points carry the six-valued polar relation `rhoAt`.  This module fixes the
four displayed anchors and the symmetric-square maps induced by the 2184 normalized invertible
two-by-two matrices.  It contains executable definitions only; separate leaves check the regular
triple orbit, the forced fourth anchor, and separation by four-anchor signatures.
-/

namespace PassantCodeQ13.Automorphisms

open RelativeConicArcs.PassantCodeQ13
open PassantCodeQ13.AssociationAlgebra
open PassantCodeQ13.MinimumWords
open PassantCodeQ13.WeightTen

/-- The indexed internal points of the normalized conic model. -/
abbrev Coordinate := Fin 78

/-- The four anchors `(1,0,2)`, `(1,1,7)`, `(1,0,7)`, and `(1,1,3)`. -/
def anchors : Fin 4 → Coordinate
  | 0 => 0
  | 1 => 8
  | 2 => 3
  | 3 => 6

/-- The image of an indexed internal point under one normalized projective matrix. -/
def matrixAction (matrix : Fin projectiveMatrices.length) (point : Coordinate) : Coordinate :=
  Fin.ofNat 78 (internalIndex (act (projectiveMatrices.get matrix) (internalAt point)))

/-- A map preserves every elliptic relation value. -/
def PreservesRho (permutation : Coordinate → Coordinate) : Prop :=
  ∀ first second, rhoAt (permutation first) (permutation second) = rhoAt first second

/-- Ordered triples with the anchor relation pattern `(10,3,9)`. -/
def patternedTriples : Finset (Coordinate × Coordinate × Coordinate) :=
  Finset.univ.filter fun triple =>
    rhoAt triple.1 triple.2.1 = 10 ∧ rhoAt triple.1 triple.2.2 = 3 ∧
      rhoAt triple.2.1 triple.2.2 = 9

/-- Images of the first three anchors under the normalized projective matrices. -/
def projectiveAnchorTriples : Finset (Coordinate × Coordinate × Coordinate) :=
  Finset.univ.image fun matrix : Fin projectiveMatrices.length =>
    (matrixAction matrix (anchors 0), matrixAction matrix (anchors 1),
      matrixAction matrix (anchors 2))

/-- The three-value signature relative to the first three anchors. -/
def firstThreeSignature (point : Coordinate) : Fin 3 → Field13 :=
  fun index => rhoAt point (anchors index.castSucc)

/-- The four-value signature, with equality to an anchor recorded as `none`. -/
def anchorSignature (point : Coordinate) : Fin 4 → Option Field13 :=
  fun index => if point = anchors index then none else some (rhoAt point (anchors index))

end PassantCodeQ13.Automorphisms
