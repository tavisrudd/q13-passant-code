import RelativeConicArcs.Gates.PassantCodeQ13
import PassantCodeQ13.WeightTen.Aggregate
import PassantCodeQ13.MinimumWords.Reconstruction
import PassantCodeQ13.MinimumWords.Exhaustion
import PassantCodeQ13.MinimumWords.RowUniqueness.Transport
import PassantCodeQ13.SemanticTransports
import PassantCodeQ13.AssociationAlgebra
import PassantCodeQ13.AssociationTransport
import PassantCodeQ13.Automorphisms.Transport
import PassantCodeQ13.StructuralUpgrade

/-!
# Aggregate finite gate for the q=13 passant code

This gate imports separately elaborated weight-ten and minimum-orbit leaves.  It establishes the
arbitrary-word reduction to the two passant-pencil profiles, the fixed-base syndrome exclusions,
four 91-element projective orbits, span rank 36 for each orbit, pair-concurrence recovery of passant
joins, and exact reconstruction of the 78 geometric passant rows.

The gate does not claim the full minimum-distance or reconstruction theorem.  Its fixed-point
weight-twelve terminal exhausts the four parity profiles and identifies their 56 solutions with
the four orbit slices; transport from the fixed point uses the symmetric-square projective action.
The concrete four-anchor transport identifies every polar-relation automorphism with one of the
2184 normalized symmetric-square projective maps.  Transport from minimum-support-hypergraph
automorphisms to polar-relation automorphisms remains part of the human concurrence argument.
-/

namespace PassantCodeQ13.Gates.Main

open PassantCodeQ13.WeightTen
open PassantCodeQ13.MinimumWords

/-- The semantic incidence map has rank 42, hence the binary passant code has dimension 36. -/
theorem incidenceRankAndCodeDimension :
    RelativeConicArcs.PassantCodeQ13.IncidenceMapHasRankFortyTwo ∧
      Module.finrank (ZMod 2) RelativeConicArcs.PassantCodeQ13.passantCode = 36 := by
  have rank := PassantCodeQ13.SemanticTransports.incidenceMap_has_rank_fortyTwo
  exact ⟨rank, RelativeConicArcs.PassantCodeQ13.passantCode_finrank_eq_thirtySix rank⟩

/-- The two weight-ten syndrome profiles are empty in every shard. -/
theorem weightTenCertificate :
    localPartitionCheck = true ∧
      (isolatedProfileCheck 0 = true ∧ isolatedProfileCheck 1 = true ∧
        isolatedProfileCheck 2 = true ∧ isolatedProfileCheck 3 = true ∧
        isolatedProfileCheck 4 = true ∧ isolatedProfileCheck 5 = true ∧
        isolatedProfileCheck 6 = true) ∧
      (cycleProfileCheck 0 = true ∧ cycleProfileCheck 1 = true ∧
        cycleProfileCheck 2 = true ∧ cycleProfileCheck 3 = true ∧
        cycleProfileCheck 4 = true ∧ cycleProfileCheck 5 = true ∧
        cycleProfileCheck 6 = true) :=
  ⟨local_partition, all_isolated_profiles_disjoint, all_cycle_profiles_disjoint⟩

/-- Every supported point of every semantic weight-ten word has the isolated or cycle pencil
profile checked by the fixed-base certificate leaves. -/
theorem arbitraryWeightTenProfileTransport
    (word : RelativeConicArcs.PassantCodeQ13.InternalPoint → ZMod 2)
    (word_mem : word ∈ RelativeConicArcs.PassantCodeQ13.passantCode)
    (weight : RelativeConicArcs.CodingBridge.hammingWeight word = 10)
    (base : RelativeConicArcs.PassantCodeQ13.InternalPoint)
    (base_mem : base ∈ RelativeConicArcs.CodingBridge.hammingSupport word) :
    RelativeConicArcs.PassantCodeQ13.WeightTen.WeightTenPencilProfile
      (RelativeConicArcs.CodingBridge.hammingSupport word) base :=
  RelativeConicArcs.Gates.PassantCodeQ13.arbitrary_weightTen_profile_transport
    word word_mem weight base base_mem

/-- The four displayed projective orbits are kernel orbits of size 91 and binary span rank 36. -/
theorem minimumOrbitCertificate :
    minimumSupportCodes.length = 364 ∧
      binaryRank (supportOrbit representativeS4) = 36 ∧
      binaryRank (supportOrbit representativeDihedralA) = 36 ∧
      binaryRank (supportOrbit representativeDihedralB) = 36 ∧
      binaryRank (supportOrbit representativeDihedralC) = 36 := by
  exact ⟨minimumSupportCodes_length, orbitS4_rank, orbitDihedralA_certificate.2.2,
    orbitDihedralB_certificate.2.2, orbitDihedralC_certificate.2.2⟩

/-- At the normalized fixed point, the four exhaustive weight-twelve pencil profiles give exactly
the four disjoint 14-support orbit slices. -/
theorem fixedPointWeightTwelveExhaustion :
    fixedPointWeightTwelveSolutions.toFinset = fixedPointOrbitSlices.toFinset ∧
      fixedPointWeightTwelveSolutions.length = 56 :=
  ⟨fixedPoint_weightTwelve_exhaustion.1, fixedPoint_weightTwelve_exhaustion.2.1⟩

/-- The order-28 fixed-point stabilizer acts transitively on each 14-support orbit slice. -/
theorem fixedPointSlicesAreStabilizerOrbits :
    fixedPointStabilizer.length = 28 ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeS4)).toFinset =
        ((supportOrbit representativeS4).filter fun support => support.testBit 0).toFinset ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeDihedralA)).toFinset =
        ((supportOrbit representativeDihedralA).filter fun support => support.testBit 0).toFinset ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeDihedralB)).toFinset =
        ((supportOrbit representativeDihedralB).filter fun support => support.testBit 0).toFinset ∧
      (fixedPointStabilizerOrbit (encodeSupport representativeDihedralC)).toFinset =
        ((supportOrbit representativeDihedralC).filter fun support => support.testBit 0).toFinset :=
  fixedPoint_slices_are_stabilizer_orbits

/-- The intrinsic seven-clique and zero-concurrence test recovers exactly the geometric passant-row
family from the four displayed minimum-support orbits. -/
theorem recoveredRowFamilyIsUnique :
    RelativeConicArcs.PassantCodeQ13.reconstructedRows
        PassantCodeQ13.MinimumWords.RowUniqueness.semanticMinimumSupports =
      RelativeConicArcs.ConicPassantCode.rowSupports
        RelativeConicArcs.PassantCodeQ13.Incident :=
  PassantCodeQ13.MinimumWords.RowUniqueness.reconstructed_rows_eq_geometric_passant_rows

/-- Each displayed minimum-word orbit spans the kernel of the rho-zero relation matrix. -/
theorem minimumOrbitsSpanRhoZeroKernel :
    LinearMap.range
        (Matrix.toLin' (PassantCodeQ13.AssociationTransport.orbitSupportMatrix
          (supportOrbit representativeS4)).transpose) =
          LinearMap.ker (Matrix.toLin'
            (PassantCodeQ13.AssociationTransport.relationLinearMatrix 0)) ∧
      LinearMap.range
        (Matrix.toLin' (PassantCodeQ13.AssociationTransport.orbitSupportMatrix
          (supportOrbit representativeDihedralA)).transpose) =
          LinearMap.ker (Matrix.toLin'
            (PassantCodeQ13.AssociationTransport.relationLinearMatrix 0)) ∧
      LinearMap.range
        (Matrix.toLin' (PassantCodeQ13.AssociationTransport.orbitSupportMatrix
          (supportOrbit representativeDihedralB)).transpose) =
          LinearMap.ker (Matrix.toLin'
            (PassantCodeQ13.AssociationTransport.relationLinearMatrix 0)) ∧
      LinearMap.range
        (Matrix.toLin' (PassantCodeQ13.AssociationTransport.orbitSupportMatrix
          (supportOrbit representativeDihedralC)).transpose) =
          LinearMap.ker (Matrix.toLin'
            (PassantCodeQ13.AssociationTransport.relationLinearMatrix 0)) :=
  PassantCodeQ13.AssociationTransport.every_minimum_orbit_spans_rhoZero_kernel

/-- Every permutation of the indexed internal points preserving the six-valued polar relation is
one of the 2184 normalized symmetric-square projective maps. -/
theorem ellipticSchemeAutomorphismsAreProjective
    (permutation : Equiv.Perm PassantCodeQ13.Automorphisms.Coordinate) :
    PassantCodeQ13.Automorphisms.PreservesRho permutation ↔
      ∃ matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length,
        permutation = PassantCodeQ13.Automorphisms.matrixEquiv matrix :=
  PassantCodeQ13.Automorphisms.preservesRho_iff_projective permutation

/-- The decoded minimum layer recovers the polarity rows from concurrence-eight neighborhoods,
has constant unary degree 56, and splits the fused concurrence-six color by pair-derived walks. -/
theorem pairOnlyReconstruction :
    RelativeConicArcs.PassantCodeQ13.PairOnlyReconstructionCertificate
      PassantCodeQ13.MinimumWords.RowUniqueness.semanticMinimumSupports :=
  PassantCodeQ13.StructuralUpgrade.pairOnlyCertificate

/-- The three punctured pencil-conic levels have size twelve and satisfy every passant parity
check. -/
theorem toricMinimumSupports :
    (PassantCodeQ13.StructuralUpgrade.toricSupport 2).card = 12 ∧
      (PassantCodeQ13.StructuralUpgrade.toricSupport 5).card = 12 ∧
      (PassantCodeQ13.StructuralUpgrade.toricSupport 11).card = 12 ∧
      PassantCodeQ13.StructuralUpgrade.HasEvenPassantIntersections
        (PassantCodeQ13.StructuralUpgrade.toricSupport 2) ∧
      PassantCodeQ13.StructuralUpgrade.HasEvenPassantIntersections
        (PassantCodeQ13.StructuralUpgrade.toricSupport 5) ∧
      PassantCodeQ13.StructuralUpgrade.HasEvenPassantIntersections
        (PassantCodeQ13.StructuralUpgrade.toricSupport 11) := by
  exact ⟨PassantCodeQ13.StructuralUpgrade.toricSupport_cards.1,
    PassantCodeQ13.StructuralUpgrade.toricSupport_cards.2.1,
    PassantCodeQ13.StructuralUpgrade.toricSupport_cards.2.2,
    PassantCodeQ13.StructuralUpgrade.toricSupport_even_passants.1,
    PassantCodeQ13.StructuralUpgrade.toricSupport_even_passants.2.1,
    PassantCodeQ13.StructuralUpgrade.toricSupport_even_passants.2.2⟩

/-- The `A₉` relation operator satisfies the hidden cubic after restriction to its image. -/
theorem hiddenFieldCubicOnImage :
    let B := PassantCodeQ13.AssociationTransport.relationLinearMatrix 9
    B ^ 4 + B ^ 3 + B = 0 :=
  PassantCodeQ13.StructuralUpgrade.hiddenField_cubic_on_image

/-- The normalized 183-coordinate incidence relation satisfies both projective-plane uniqueness
axioms and has a fourteen-point determinant conic. -/
theorem ambientPlaneIncidence :
    Fintype.card PassantCodeQ13.StructuralUpgrade.PlaneCoordinate = 183 ∧
      (Finset.univ.filter fun point : PassantCodeQ13.StructuralUpgrade.PlaneCoordinate =>
        RelativeConicArcs.PassantCodeQ13.pointDiscriminant point.1 = 0).card = 14 ∧
      (∀ first second : PassantCodeQ13.StructuralUpgrade.PlaneCoordinate,
        first ≠ second →
          ∃! line : PassantCodeQ13.StructuralUpgrade.PlaneCoordinate,
            PassantCodeQ13.StructuralUpgrade.PlaneIncident line first ∧
            PassantCodeQ13.StructuralUpgrade.PlaneIncident line second) ∧
      (∀ first second : PassantCodeQ13.StructuralUpgrade.PlaneCoordinate,
        first ≠ second →
          ∃! point : PassantCodeQ13.StructuralUpgrade.PlaneCoordinate,
            PassantCodeQ13.StructuralUpgrade.PlaneIncident first point ∧
            PassantCodeQ13.StructuralUpgrade.PlaneIncident second point) := by
  exact ⟨PassantCodeQ13.StructuralUpgrade.planeCoordinate_card,
    PassantCodeQ13.StructuralUpgrade.determinantConic_card,
    PassantCodeQ13.StructuralUpgrade.uniqueLine_through_two_points,
    PassantCodeQ13.StructuralUpgrade.uniquePoint_on_two_lines⟩

end PassantCodeQ13.Gates.Main
