import PassantCodeQ13.MinimumWords.RowUniqueness.DecodeInjective

/-!
# Semantic transport for encoded triple concurrence

Counting encoded supports containing three displayed indices agrees with semantic concurrence in
the decoded support hypergraph.  The proof uses injectivity of decoding and does not enumerate all
point triples.
-/

namespace PassantCodeQ13.MinimumWords.RowUniqueness

open Finset
open RelativeConicArcs.PassantCodeQ13

/-- Boolean test that an encoded support contains three displayed indices. -/
def encodedContainsTriple (support : Nat) (first second third : Fin 78) : Bool :=
  support.testBit first.1 && support.testBit second.1 && support.testBit third.1

/-- On a duplicate-free list, Boolean counting is cardinality of the corresponding filtered
finite set. -/
theorem countP_eq_card_filter_toFinset {Element : Type*} [DecidableEq Element]
    (elements : List Element) (predicate : Element → Bool) (nodup : elements.Nodup) :
    elements.countP predicate =
      (elements.toFinset.filter fun element => predicate element = true).card := by
  induction elements with
  | nil => simp
  | cons head tail induction_hypothesis =>
      have head_not_mem : head ∉ tail := (List.nodup_cons.mp nodup).1
      have tail_nodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      rw [List.countP_cons, induction_hypothesis tail_nodup]
      simp only [List.toFinset_cons]
      by_cases selected : predicate head = true
      · rw [Finset.filter_insert]
        simp [selected, head_not_mem]
      · have rejected : predicate head = false := Bool.eq_false_of_not_eq_true selected
        rw [Finset.filter_insert]
        simp [rejected]

/-- Encoded triple concurrence agrees with semantic concurrence after support decoding. -/
theorem indexedTripleConcurrence_eq_semantic_direct
    (firstIndex secondIndex thirdIndex : Fin 78) :
    indexedTripleConcurrence (internalPointAt firstIndex) (internalPointAt secondIndex)
        (internalPointAt thirdIndex) =
      RelativeConicArcs.ConicPassantCode.tripleConcurrence semanticMinimumSupports
        (internalPointAt firstIndex) (internalPointAt secondIndex)
        (internalPointAt thirdIndex) := by
  let sourceSupports := minimumSupportCodes.toFinset.filter fun support =>
    encodedContainsTriple support firstIndex secondIndex thirdIndex = true
  let semanticSupports := semanticMinimumSupports.filter fun support =>
    internalPointAt firstIndex ∈ support ∧ internalPointAt secondIndex ∈ support ∧
      internalPointAt thirdIndex ∈ support
  have image_eq : sourceSupports.image decodedSupport = semanticSupports := by
    ext support
    constructor
    · intro support_mem
      obtain ⟨encoded, encoded_mem, rfl⟩ := Finset.mem_image.mp support_mem
      have encoded_data := Finset.mem_filter.mp encoded_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨encoded, encoded_data.1, rfl⟩, ?_⟩
      simpa [encodedContainsTriple, Bool.and_eq_true, mem_decodedSupport, and_assoc] using
        encoded_data.2
    · intro support_mem
      have semantic_data := Finset.mem_filter.mp support_mem
      obtain ⟨encoded, encoded_mem, rfl⟩ := Finset.mem_image.mp semantic_data.1
      apply Finset.mem_image.mpr
      refine ⟨encoded, Finset.mem_filter.mpr ⟨encoded_mem, ?_⟩, rfl⟩
      simpa [encodedContainsTriple, Bool.and_eq_true, mem_decodedSupport, and_assoc] using
        semantic_data.2
  have source_injective : Set.InjOn decodedSupport sourceSupports :=
    decodedSupport_injOn.mono (Finset.filter_subset _ _)
  have minimumSupports_nodup : minimumSupportCodes.Nodup := by
    native_decide
  unfold indexedTripleConcurrence tripleConcurrenceIn
  simp only [internalPointIndex_internalPointAt]
  change minimumSupportCodes.countP
      (fun support => encodedContainsTriple support firstIndex secondIndex thirdIndex) = _
  rw [countP_eq_card_filter_toFinset minimumSupportCodes
    (fun support => encodedContainsTriple support firstIndex secondIndex thirdIndex)
    minimumSupports_nodup]
  change sourceSupports.card = semanticSupports.card
  rw [← image_eq, Finset.card_image_of_injOn source_injective]

/-- The executable concurrence count agrees with semantic concurrence at arbitrary points. -/
theorem indexedTripleConcurrence_eq_semantic
    (first second third : InternalPoint) :
    indexedTripleConcurrence first second third =
      RelativeConicArcs.ConicPassantCode.tripleConcurrence semanticMinimumSupports
        first second third := by
  obtain ⟨firstIndex, rfl⟩ := internalPointAt_bijective.surjective first
  obtain ⟨secondIndex, rfl⟩ := internalPointAt_bijective.surjective second
  obtain ⟨thirdIndex, rfl⟩ := internalPointAt_bijective.surjective third
  exact indexedTripleConcurrence_eq_semantic_direct firstIndex secondIndex thirdIndex

/-- Counting displayed vertices selected by one encoded support is cardinality of the semantic
intersection after decoding. -/
theorem supportIntersectionCount_eq_card (support : Nat) (vertices : Finset InternalPoint) :
    (verticesInOrder vertices).countP
        (fun point => support.testBit (internalPointIndex point)) =
      (decodedSupport support ∩ vertices).card := by
  rw [countP_eq_card_filter_toFinset (verticesInOrder vertices)
    (fun point => support.testBit (internalPointIndex point))
    (verticesInOrder_nodup vertices)]
  congr 1
  ext point
  obtain ⟨index, rfl⟩ := internalPointAt_bijective.surjective point
  simp [verticesInOrder_toFinset, mem_decodedSupport,
    internalPointIndex_internalPointAt, and_comm]

end PassantCodeQ13.MinimumWords.RowUniqueness
