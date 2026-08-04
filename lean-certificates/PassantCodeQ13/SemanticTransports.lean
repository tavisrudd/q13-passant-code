import PassantCodeQ13.Rank
import PassantCodeQ13.RankTransportData
import RelativeConicArcs.PassantCodeQ13.Rank

/-!
# Semantic transports for the finite passant-code certificates

This module connects executable certificate data to the linear-algebraic objects used in the
passant-code theorem.  Each theorem states a concrete correspondence; kernel reduction is used
only after the correspondence has been expressed in the semantic types.
-/

namespace PassantCodeQ13.SemanticTransports

open RelativeConicArcs.PassantCodeQ13

/-- The first 42 displayed incidence columns. -/
def basisColumn (index : Fin 42) : PassantLine → ZMod 2 :=
  RelativeConicArcs.ConicPassantCode.incidenceColumn Incident
    (internalPointAt ⟨index.1, Nat.lt_trans index.2 (by decide)⟩)

/-- Apply one recovery functional to a binary vector on the passant lines. -/
def recoverCoefficient (index : Fin 42) (vector : PassantLine → ZMod 2) : ZMod 2 :=
  ∑ lineIndex : Fin 42,
    if (RankTransportData.recoveryMask index).testBit lineIndex.1 then
      vector (passantLineAt ⟨lineIndex.1, Nat.lt_trans lineIndex.2 (by decide)⟩)
    else 0

/-- The recovery functional as a binary linear map. -/
def recoverLinearMap (index : Fin 42) :
    (PassantLine → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ lineIndex : Fin 42,
    if (RankTransportData.recoveryMask index).testBit lineIndex.1 then
      (LinearMap.proj (passantLineAt
        ⟨lineIndex.1, Nat.lt_trans lineIndex.2 (by decide)⟩) :
          (PassantLine → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    else 0

@[simp] theorem recoverLinearMap_apply (index : Fin 42)
    (vector : PassantLine → ZMod 2) :
    recoverLinearMap index vector = recoverCoefficient index vector := by
  simp only [recoverLinearMap, recoverCoefficient, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro lineIndex _
  by_cases selected : (RankTransportData.recoveryMask index).testBit lineIndex.1 <;>
    simp [selected]

/-- The recovery masks are left inverse to the first 42 incidence columns. -/
theorem recoverCoefficient_basisColumn : ∀ row column : Fin 42,
    recoverCoefficient row (basisColumn column) = if row = column then 1 else 0 := by
  decide +kernel

/-- The first 42 displayed incidence columns are linearly independent over the binary field. -/
theorem basisColumn_linearIndependent :
    LinearIndependent (ZMod 2) basisColumn := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients sum_zero row
  have recovered := congrArg (recoverLinearMap row) sum_zero
  simp only [map_sum, map_smul, map_zero, recoverLinearMap_apply] at recovered
  simp_rw [recoverCoefficient_basisColumn] at recovered
  simpa using recovered

/-- Every displayed incidence column is the certified binary combination of the first 42. -/
theorem incidenceColumn_expansion : ∀ index : Fin 78,
    RelativeConicArcs.ConicPassantCode.incidenceColumn Incident (internalPointAt index) =
      ∑ basisIndex : Fin 42,
        if (RankTransportData.columnExpansionMask index).testBit basisIndex.1 then
          basisColumn basisIndex else 0 := by
  decide +kernel

/-- The first 42 columns span all semantic incidence columns. -/
theorem incidenceColumn_span_eq_basisColumn_span :
    Submodule.span (ZMod 2)
        (Set.range (RelativeConicArcs.ConicPassantCode.incidenceColumn Incident)) =
      Submodule.span (ZMod 2) (Set.range basisColumn) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro column ⟨point, rfl⟩
    obtain ⟨index, rfl⟩ := internalPointAt_bijective.surjective point
    rw [incidenceColumn_expansion]
    apply Submodule.sum_mem
    intro basisIndex _
    split
    · exact Submodule.subset_span ⟨basisIndex, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro column ⟨index, rfl⟩
    exact Submodule.subset_span
      ⟨internalPointAt ⟨index.1, Nat.lt_trans index.2 (by decide)⟩, rfl⟩

/-- The executable elimination certificate transports to rank 42 of the semantic incidence map. -/
theorem incidenceMap_has_rank_fortyTwo : IncidenceMapHasRankFortyTwo := by
  rw [IncidenceMapHasRankFortyTwo, incidenceMap,
    RelativeConicArcs.CodingBridge.parityCheckMap, Fintype.range_linearCombination,
    incidenceColumn_span_eq_basisColumn_span]
  exact finrank_span_eq_card basisColumn_linearIndependent

end PassantCodeQ13.SemanticTransports
