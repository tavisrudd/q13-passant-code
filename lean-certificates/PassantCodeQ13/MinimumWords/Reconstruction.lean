import PassantCodeQ13.MinimumWords.OrbitS4
import PassantCodeQ13.MinimumWords.OrbitDihedral

/-!
# Concurrence checks for the four minimum-word orbits

The four 91-element projective orbits are joined into a 364-support hypergraph.  Native evaluation
checks pair concurrence against the geometric passant-join relation and checks that every geometric
passant row is a seven-set all of whose triples have concurrence zero.

This finite leaf proves the forward reconstruction signatures.  It does not by itself prove that no
additional seven-clique has the same zero-triple property; that uniqueness statement remains an
explicit field of the shared `MinimumLayerCertificate` interface.
-/

namespace PassantCodeQ13.MinimumWords

open PassantCodeQ13.WeightTen

/-- The union of the four displayed projective support orbits. -/
def minimumSupportCodes : List Nat :=
  (supportOrbit representativeS4 ++ supportOrbit representativeDihedralA ++
    supportOrbit representativeDihedralB ++ supportOrbit representativeDihedralC).eraseDups

/-- Pair concurrence in an explicitly supplied encoded support hypergraph. -/
def pairConcurrenceIn (supports : List Nat) (first second : Nat) : Nat :=
  supports.countP fun support => support.testBit first && support.testBit second

/-- Triple concurrence in an explicitly supplied encoded support hypergraph. -/
def tripleConcurrenceIn (supports : List Nat) (first second third : Nat) : Nat :=
  supports.countP fun support =>
    support.testBit first && support.testBit second && support.testBit third

/-- Whether two indexed internal points lie on a common passant. -/
def hasPassantJoin (first second : Nat) : Bool :=
  (List.range 78).any fun line => incidentAt line first && incidentAt line second

/-- The 78 geometric passant-row supports, encoded as bit sets of internal-point indices. -/
def passantRowCodes : List Nat :=
  (List.range 78).map fun line =>
    (List.range 78).foldl (fun support point =>
      if incidentAt line point then support ||| (1 <<< point) else support) 0

/-- Every geometric passant row has seven points and zero concurrence on each of its triples. -/
def passantRowTripleCheck : Bool :=
  let supports := minimumSupportCodes
  passantRowCodes.all fun row =>
    let points := (List.range 78).filter row.testBit
    points.length == 7 &&
      (points.sublistsLen 3).all fun triple =>
        match triple with
        | [first, second, third] => tripleConcurrenceIn supports first second third == 0
        | _ => false

/-- Exhaustive pair-concurrence comparison with geometric passant joins. -/
def pairRecoveryCheck : Bool :=
  let supports := minimumSupportCodes
  (List.range 78).all (fun first =>
    (List.range 78).all fun second =>
      first == second ||
        (hasPassantJoin first second ==
          ([7, 9, 12].contains (pairConcurrenceIn supports first second))))

/-- The four projective orbits contain 364 distinct supports. -/
theorem minimumSupportCodes_length : minimumSupportCodes.length = 364 := by
  native_decide

/-- Pair concurrence recovers whether the join of two distinct internal points is passant. -/
theorem pair_concurrence_recovers_passant_join :
    pairRecoveryCheck = true := by
  native_decide

/-- The 78 geometric passant rows have the required seven-point zero-triple signatures. -/
theorem geometric_rows_have_zero_triple_signatures :
    passantRowCodes.eraseDups.length = 78 ∧ passantRowTripleCheck = true := by
  native_decide

end PassantCodeQ13.MinimumWords
