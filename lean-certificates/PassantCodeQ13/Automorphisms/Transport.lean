import PassantCodeQ13.Automorphisms.TripleOrbit
import PassantCodeQ13.Automorphisms.FourthAnchor
import PassantCodeQ13.Automorphisms.Signatures
import RelativeConicArcs.PassantCodeQ13.LogicalSpine

/-!
# Concrete four-anchor transport

The three bounded anchor leaves feed the abstract four-anchor closure.  Every permutation of the
78 indexed internal points preserving the polar relation is one of the symmetric-square maps from
the 2184 normalized invertible matrices.  Conversely every such matrix map preserves the relation.
Native evaluation is confined to the three imported leaves; the transport below is symbolic.
-/

namespace PassantCodeQ13.Automorphisms

open RelativeConicArcs.PassantCodeQ13.LogicalSpine
open PassantCodeQ13.AssociationAlgebra

/-- The projective matrix action as an equivalence of the indexed internal points. -/
noncomputable def matrixEquiv
    (matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length) : Equiv.Perm Coordinate :=
  Equiv.ofBijective (matrixAction matrix) (matrixAction_bijective matrix)

/-- The underlying map of the projective equivalence is the executable symmetric-square action. -/
@[simp] theorem matrixEquiv_apply
    (matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length) (point : Coordinate) :
    matrixEquiv matrix point = matrixAction matrix point := rfl

set_option maxRecDepth 10000 in
/-- Every relation-preserving coordinate permutation is induced by one normalized invertible
two-by-two matrix through the symmetric-square action. -/
theorem preservesRho_is_projective
    (permutation : Equiv.Perm Coordinate) (preserves : PreservesRho permutation) :
    ∃ matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length,
      permutation = matrixEquiv matrix := by
  suffices classified :
      ∃ matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length,
        (permutation : Coordinate → Coordinate) = matrixEquiv matrix by
    obtain ⟨matrix, equality⟩ := classified
    exact ⟨matrix, Equiv.ext fun point => congrFun equality point⟩
  let IsAutomorphism := fun current : Coordinate → Coordinate =>
    PreservesRho current ∧ Function.Bijective current
  apply four_anchor_transport_rigidity
    (action := fun matrix => matrixEquiv matrix)
    (Preserves := IsAutomorphism)
    (first := anchors 0) (second := anchors 1) (third := anchors 2) (fourth := anchors 3)
  · intro current current_preserves
    have target_mem :
        (current (anchors 0), current (anchors 1), current (anchors 2)) ∈ patternedTriples := by
      simp only [patternedTriples, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(current_preserves.1 _ _).trans anchorTriplePattern.1,
        (current_preserves.1 _ _).trans anchorTriplePattern.2.1,
        (current_preserves.1 _ _).trans anchorTriplePattern.2.2⟩
    rw [← projectiveAnchorTriples_eq_patterned.1] at target_mem
    obtain ⟨matrix, _, matrix_matches⟩ := Finset.mem_image.mp target_mem
    let normalized : Coordinate → Coordinate := fun point =>
      (matrixEquiv matrix)⁻¹ (current point)
    refine ⟨matrix, normalized, ?_, ?_, ?_, ?_, ?_⟩
    · ext point
      simp [normalized]
    · constructor
      · intro first second
        have matrix_preserves := matrixAction_preservesRho matrix
        have inverse_preserves :
            rhoAt ((matrixEquiv matrix)⁻¹ (current first))
                ((matrixEquiv matrix)⁻¹ (current second)) =
              rhoAt (current first) (current second) := by
          calc
            _ = rhoAt
                (matrixAction matrix ((matrixEquiv matrix)⁻¹ (current first)))
                (matrixAction matrix ((matrixEquiv matrix)⁻¹ (current second))) :=
              (matrix_preserves _ _).symm
            _ = _ := by
              rw [← matrixEquiv_apply, ← matrixEquiv_apply]
              simp
        exact inverse_preserves.trans (current_preserves.1 first second)
      · exact (matrixEquiv matrix).symm.bijective.comp current_preserves.2
    · apply (matrixEquiv matrix).injective
      simpa [normalized] using (congrArg Prod.fst matrix_matches).symm
    · apply (matrixEquiv matrix).injective
      simpa [normalized] using (congrArg (fun triple => triple.2.1) matrix_matches).symm
    · apply (matrixEquiv matrix).injective
      simpa [normalized] using (congrArg (fun triple => triple.2.2) matrix_matches).symm
  · intro current current_preserves fixes_first fixes_second fixes_third
    apply (firstThreeSignature_eq_iff (current (anchors 3))).mp
    calc
      firstThreeSignature (current (anchors 3)) = firstThreeSignature (anchors 3) := by
        funext index
        fin_cases index
        · change rhoAt (current (anchors 3)) (anchors 0) = _
          rw [← fixes_first]
          exact current_preserves.1 _ _
        · change rhoAt (current (anchors 3)) (anchors 1) = _
          rw [← fixes_second]
          exact current_preserves.1 _ _
        · change rhoAt (current (anchors 3)) (anchors 2) = _
          rw [← fixes_third]
          exact current_preserves.1 _ _
      _ = ![3, 1, 9] := (firstThreeSignature_eq_iff (anchors 3)).2 rfl
  · intro current current_preserves fixes_first fixes_second fixes_third fixes_fourth
    funext point
    apply anchorSignature_injective
    have signature_at_fixed_anchor (anchor : Coordinate)
        (fixed : current anchor = anchor) :
        (if current point = anchor then none else some (rhoAt (current point) anchor)) =
          if point = anchor then none else some (rhoAt point anchor) := by
      by_cases point_fixed : point = anchor
      · subst point
        simp [fixed]
      · have image_not_anchor : current point ≠ anchor := by
          intro image_fixed
          apply point_fixed
          apply current_preserves.2.1
          exact image_fixed.trans fixed.symm
        simp [point_fixed, image_not_anchor]
        calc
          rhoAt (current point) anchor = rhoAt (current point) (current anchor) :=
            congrArg (fun second : Coordinate => rhoAt (current point) second) fixed.symm
          _ = rhoAt point anchor := current_preserves.1 point anchor
    funext index
    fin_cases index
    · exact signature_at_fixed_anchor (anchors 0) fixes_first
    · exact signature_at_fixed_anchor (anchors 1) fixes_second
    · exact signature_at_fixed_anchor (anchors 2) fixes_third
    · exact signature_at_fixed_anchor (anchors 3) fixes_fourth

  exact ⟨preserves, permutation.bijective⟩

/-- The relation-preserving permutations are exactly the 2184 normalized symmetric-square maps. -/
theorem preservesRho_iff_projective
    (permutation : Equiv.Perm Coordinate) :
    PreservesRho permutation ↔
      ∃ matrix : Fin PassantCodeQ13.MinimumWords.projectiveMatrices.length,
        permutation = matrixEquiv matrix := by
  constructor
  · exact preservesRho_is_projective permutation
  · rintro ⟨matrix, rfl⟩
    intro first second
    exact matrixAction_preservesRho matrix first second

end PassantCodeQ13.Automorphisms
