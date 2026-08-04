import PassantCodeQ13.AssociationTransport.RelationSquares
import PassantCodeQ13.AssociationTransport.OrbitS4
import PassantCodeQ13.AssociationTransport.OrbitDihedralA
import PassantCodeQ13.AssociationTransport.OrbitDihedralB
import PassantCodeQ13.AssociationTransport.OrbitDihedralC
import RelativeConicArcs.PassantCodeQ13.LogicalSpine

/-!
# Orbit Gram matrices and the binary association action

Eight bounded execution leaves check four relation identities and the Gram/kernel pair for each
orbit.  Their ordinary matrix equalities feed the abstract association-kernel argument, proving
that each of the
four orbit row spaces is exactly the kernel of the rho-zero relation matrix.  This aggregator has
no native evaluation.

Polarity identifies that rho-zero matrix with the passant incidence matrix up to row order.  This
module fixes the point-vector convention: matrices act on coordinate columns, while the transpose
of a 91-by-78 orbit-support matrix maps orbit coefficients to codewords.
-/

namespace PassantCodeQ13.AssociationTransport

open PassantCodeQ13.AssociationAlgebra
open PassantCodeQ13.MinimumWords
open RelativeConicArcs.PassantCodeQ13

private theorem relationRangeEqKernel
    (B B2 B4 : Matrix Coordinate Coordinate (ZMod 2))
    (A0B : relationLinearMatrix 0 * B = 0)
    (B_squared : B * B = B2)
    (B2_squared : B2 * B2 = B4)
    (A0_squared : relationLinearMatrix 0 * relationLinearMatrix 0 =
      1 + B + B2 + B4) :
    LinearMap.range (Matrix.toLin' B) =
      LinearMap.ker (Matrix.toLin' (relationLinearMatrix 0)) := by
  apply RelativeConicArcs.PassantCodeQ13.LogicalSpine.relation_range_eq_kernel
      (Matrix.toLin' (relationLinearMatrix 0)) (Matrix.toLin' B)
      (Matrix.toLin' B2) (Matrix.toLin' B4)
  · simpa using congrArg Matrix.toLin' A0B
  · simpa using congrArg Matrix.toLin' B_squared
  · simpa using congrArg Matrix.toLin' B2_squared
  · simpa using congrArg Matrix.toLin' A0_squared

private theorem orbitSpansKernel
    (orbit : List Nat) (B B2 B4 : Matrix Coordinate Coordinate (ZMod 2))
    (Gram : (orbitSupportMatrix orbit).transpose * orbitSupportMatrix orbit = B)
    (rows_zero : relationLinearMatrix 0 * (orbitSupportMatrix orbit).transpose = 0)
    (B_squared : B * B = B2)
    (B2_squared : B2 * B2 = B4)
    (A0_squared : relationLinearMatrix 0 * relationLinearMatrix 0 =
      1 + B + B2 + B4) :
    LinearMap.range (Matrix.toLin' (orbitSupportMatrix orbit).transpose) =
      LinearMap.ker (Matrix.toLin' (relationLinearMatrix 0)) := by
  let orbitRows := Matrix.toLin' (orbitSupportMatrix orbit).transpose
  let transposeRows := Matrix.toLin' (orbitSupportMatrix orbit)
  have A0B : relationLinearMatrix 0 * B = 0 := by
    rw [← Gram, ← Matrix.mul_assoc, rows_zero]
    ext
    simp
  apply RelativeConicArcs.PassantCodeQ13.LogicalSpine.factorization_forces_orbit_span
      (Matrix.toLin' (relationLinearMatrix 0)) (Matrix.toLin' B) orbitRows transposeRows
  · simpa [orbitRows, transposeRows] using congrArg Matrix.toLin' Gram
  · exact relationRangeEqKernel B B2 B4 A0B B_squared B2_squared A0_squared
  · rintro vector ⟨source, rfl⟩
    rw [LinearMap.mem_ker]
    have composition_zero :
        (Matrix.toLin' (relationLinearMatrix 0)).comp orbitRows = 0 := by
      simpa [orbitRows] using congrArg Matrix.toLin' rows_zero
    simpa using LinearMap.congr_fun composition_zero source

/-- Each displayed minimum-word orbit spans the rho-zero relation kernel. -/
theorem every_minimum_orbit_spans_rhoZero_kernel :
    LinearMap.range
        (Matrix.toLin' (orbitSupportMatrix (supportOrbit representativeS4)).transpose) =
          LinearMap.ker (Matrix.toLin' (relationLinearMatrix 0)) ∧
      LinearMap.range
        (Matrix.toLin' (orbitSupportMatrix (supportOrbit representativeDihedralA)).transpose) =
          LinearMap.ker (Matrix.toLin' (relationLinearMatrix 0)) ∧
      LinearMap.range
        (Matrix.toLin' (orbitSupportMatrix (supportOrbit representativeDihedralB)).transpose) =
          LinearMap.ker (Matrix.toLin' (relationLinearMatrix 0)) ∧
      LinearMap.range
        (Matrix.toLin' (orbitSupportMatrix (supportOrbit representativeDihedralC)).transpose) =
          LinearMap.ker (Matrix.toLin' (relationLinearMatrix 0)) := by
  have identities := relation_matrix_identities
  have symmetricOrbit := orbitS4_Gram_and_kernel
  have firstDihedral := orbitDihedralA_Gram_and_kernel
  have secondDihedral := orbitDihedralB_Gram_and_kernel
  have thirdDihedral := orbitDihedralC_Gram_and_kernel
  have secondSquare :
      relationLinearMatrix 0 * relationLinearMatrix 0 =
        1 + relationLinearMatrix 12 + relationLinearMatrix 9 + relationLinearMatrix 10 := by
    simpa only [add_assoc, add_comm, add_left_comm] using identities.1
  have thirdSquare :
      relationLinearMatrix 0 * relationLinearMatrix 0 =
        1 + relationLinearMatrix 10 + relationLinearMatrix 12 + relationLinearMatrix 9 := by
    simpa only [add_assoc, add_comm, add_left_comm] using identities.1
  dsimp only at symmetricOrbit firstDihedral secondDihedral thirdDihedral
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact orbitSpansKernel _ (relationLinearMatrix 9) (relationLinearMatrix 10)
      (relationLinearMatrix 12) symmetricOrbit.1 symmetricOrbit.2 identities.2.1
      identities.2.2.1 identities.1
  · exact orbitSpansKernel _ (relationLinearMatrix 9) (relationLinearMatrix 10)
      (relationLinearMatrix 12) firstDihedral.1 firstDihedral.2 identities.2.1
      identities.2.2.1 identities.1
  · exact orbitSpansKernel _ (relationLinearMatrix 12) (relationLinearMatrix 9)
      (relationLinearMatrix 10) secondDihedral.1 secondDihedral.2 identities.2.2.2
      identities.2.1 secondSquare
  · exact orbitSpansKernel _ (relationLinearMatrix 10) (relationLinearMatrix 12)
      (relationLinearMatrix 9) thirdDihedral.1 thirdDihedral.2 identities.2.2.1
      identities.2.2.2 thirdSquare

end PassantCodeQ13.AssociationTransport
