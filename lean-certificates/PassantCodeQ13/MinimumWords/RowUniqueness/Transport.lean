import PassantCodeQ13.MinimumWords.RowUniqueness.Aggregate
import PassantCodeQ13.MinimumWords.RowUniqueness.GeometricRows

/-!
# Semantic uniqueness of the reconstructed passant rows

The indexed local-extension certificates are transported to the normalized internal-point type.
Every admissible seven-set contains a three-point seed; its other four points occur as one of the
checked four-sublists of that seed's extension pool.  The shared seven-set transport theorem then
identifies the intrinsically reconstructed family with the geometric passant rows.
-/

namespace PassantCodeQ13.MinimumWords.RowUniqueness

open Finset
open RelativeConicArcs.PassantCodeQ13

/-- The executable candidate predicate is exactly the semantic passant-clique and zero-triple
condition. -/
theorem reconstructionCandidateCheck_eq_true_iff (vertices : Finset InternalPoint) :
    reconstructionCandidateCheck vertices = true ↔
      IsPassantClique vertices ∧
        ∀ first ∈ vertices, ∀ second ∈ vertices, ∀ third ∈ vertices,
          first ≠ second → first ≠ third → second ≠ third →
            RelativeConicArcs.ConicPassantCode.tripleConcurrence
              semanticMinimumSupports first second third = 0 := by
  let pairCheck := (verticesInOrder vertices).all fun first =>
    (verticesInOrder vertices).all fun second =>
      if first == second then true else indexedPassantJoin first second
  let supportCheck := minimumSupportCodes.all fun support =>
    (verticesInOrder vertices).countP
      (fun point => support.testBit (internalPointIndex point)) ≤ 2
  have pair_iff : pairCheck = true ↔ IsPassantClique vertices := by
    constructor
    · intro pair_check first first_mem second second_mem first_ne_second
      have checked := (List.all_eq_true.mp
        (List.all_eq_true.mp pair_check first
          ((mem_verticesInOrder first vertices).mpr first_mem))) second
            ((mem_verticesInOrder second vertices).mpr second_mem)
      exact (indexedPassantJoin_eq_true_iff first second).mp
        (by simpa [first_ne_second] using checked)
    · intro pair_condition
      apply List.all_eq_true.mpr
      intro first first_mem
      apply List.all_eq_true.mpr
      intro second second_mem
      by_cases first_eq_second : first = second
      · simp [first_eq_second]
      · have semantic_join := pair_condition first
          ((mem_verticesInOrder first vertices).mp first_mem) second
          ((mem_verticesInOrder second vertices).mp second_mem) first_eq_second
        have executable_join := (indexedPassantJoin_eq_true_iff first second).mpr semantic_join
        simp [first_eq_second, executable_join]
  have support_iff : supportCheck = true ↔
      ∀ first ∈ vertices, ∀ second ∈ vertices, ∀ third ∈ vertices,
        first ≠ second → first ≠ third → second ≠ third →
          RelativeConicArcs.ConicPassantCode.tripleConcurrence
            semanticMinimumSupports first second third = 0 := by
    constructor
    · intro support_check first first_mem second second_mem third third_mem
        first_ne_second first_ne_third second_ne_third
      unfold RelativeConicArcs.ConicPassantCode.tripleConcurrence
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro support support_mem support_contains
      obtain ⟨encoded, encoded_mem, rfl⟩ := Finset.mem_image.mp support_mem
      have checked := (List.all_eq_true.mp support_check) encoded
        (List.mem_toFinset.mp encoded_mem)
      have checked_card : (decodedSupport encoded ∩ vertices).card ≤ 2 := by
        rw [← supportIntersectionCount_eq_card]
        exact of_decide_eq_true checked
      have triple_subset : ({first, second, third} : Finset InternalPoint) ⊆
          decodedSupport encoded ∩ vertices := by
        intro point point_mem
        simp only [mem_insert, mem_singleton] at point_mem
        rcases point_mem with rfl | rfl | rfl
        · exact Finset.mem_inter.mpr ⟨support_contains.1, first_mem⟩
        · exact Finset.mem_inter.mpr ⟨support_contains.2.1, second_mem⟩
        · exact Finset.mem_inter.mpr ⟨support_contains.2.2, third_mem⟩
      have triple_card : ({first, second, third} : Finset InternalPoint).card = 3 := by
        simp [first_ne_second, first_ne_third, second_ne_third]
      have := Finset.card_mono triple_subset
      omega
    · intro triple_condition
      apply List.all_eq_true.mpr
      intro encoded encoded_mem
      apply decide_eq_true
      rw [supportIntersectionCount_eq_card]
      by_contra too_large
      have more_than_two : 2 < (decodedSupport encoded ∩ vertices).card := by omega
      obtain ⟨first, second, third, first_mem, second_mem, third_mem,
        first_ne_second, first_ne_third, second_ne_third⟩ :=
          Finset.two_lt_card_iff.mp more_than_two
      have semantic_zero := triple_condition first (Finset.mem_inter.mp first_mem).2
        second (Finset.mem_inter.mp second_mem).2 third (Finset.mem_inter.mp third_mem).2
        first_ne_second first_ne_third second_ne_third
      unfold RelativeConicArcs.ConicPassantCode.tripleConcurrence at semantic_zero
      have encoded_semantic : decodedSupport encoded ∈ semanticMinimumSupports :=
        Finset.mem_image.mpr ⟨encoded, List.mem_toFinset.mpr encoded_mem, rfl⟩
      have filtered_nonempty :
          (semanticMinimumSupports.filter fun support =>
            first ∈ support ∧ second ∈ support ∧ third ∈ support).Nonempty := by
        refine ⟨decodedSupport encoded, Finset.mem_filter.mpr ⟨encoded_semantic, ?_⟩⟩
        exact ⟨(Finset.mem_inter.mp first_mem).1, (Finset.mem_inter.mp second_mem).1,
          (Finset.mem_inter.mp third_mem).1⟩
      exact (Finset.card_ne_zero.mpr filtered_nonempty) semantic_zero
  change (if pairCheck then supportCheck else false) = true ↔ _
  by_cases pair_check : pairCheck = true
  · have pair_condition := pair_iff.mp pair_check
    simp [pair_check, pair_condition, support_iff]
  · have pair_condition : ¬ IsPassantClique vertices :=
      fun condition => pair_check (pair_iff.mpr condition)
    simp [pair_check, pair_condition]

/-- The intrinsic candidate condition passes to subsets. -/
theorem reconstructionCandidateCheck_mono {smaller larger : Finset InternalPoint}
    (subset : smaller ⊆ larger) (larger_check : reconstructionCandidateCheck larger = true) :
    reconstructionCandidateCheck smaller = true := by
  apply (reconstructionCandidateCheck_eq_true_iff smaller).mpr
  have semantic := (reconstructionCandidateCheck_eq_true_iff larger).mp larger_check
  constructor
  · intro first first_mem second second_mem first_ne_second
    exact semantic.1 first (subset first_mem) second (subset second_mem) first_ne_second
  · intro first first_mem second second_mem third third_mem
      first_ne_second first_ne_third second_ne_third
    exact semantic.2 first (subset first_mem) second (subset second_mem) third
      (subset third_mem) first_ne_second first_ne_third second_ne_third

/-- Every semantic admissible seven-set occurs in the geometric passant-row family. -/
theorem admissible_seven_set_is_geometric_row
    (vertices : Finset InternalPoint)
    (vertices_card : vertices.card = 7)
    (vertices_clique : IsPassantClique vertices)
    (vertices_zero : ∀ first ∈ vertices, ∀ second ∈ vertices, ∀ third ∈ vertices,
      first ≠ second → first ≠ third → second ≠ third →
        RelativeConicArcs.ConicPassantCode.tripleConcurrence
          semanticMinimumSupports first second third = 0) :
    vertices ∈ RelativeConicArcs.ConicPassantCode.rowSupports Incident := by
  have more_than_two : 2 < vertices.card := by omega
  obtain ⟨first, second, third, first_mem, second_mem, third_mem,
    first_ne_second, first_ne_third, second_ne_third⟩ :=
      Finset.two_lt_card_iff.mp more_than_two
  obtain ⟨firstIndex, rfl⟩ := internalPointAt_bijective.surjective first
  obtain ⟨secondIndex, rfl⟩ := internalPointAt_bijective.surjective second
  obtain ⟨thirdIndex, rfl⟩ := internalPointAt_bijective.surjective third
  have indices_distinct : firstIndex ≠ secondIndex ∧ firstIndex ≠ thirdIndex ∧
      secondIndex ≠ thirdIndex := by
    exact ⟨fun equality => first_ne_second (congrArg internalPointAt equality),
      fun equality => first_ne_third (congrArg internalPointAt equality),
      fun equality => second_ne_third (congrArg internalPointAt equality)⟩
  have seed_subset : indexedSeed firstIndex secondIndex thirdIndex ⊆ vertices := by
    intro point point_mem
    simp only [indexedSeed, mem_insert, mem_singleton] at point_mem
    rcases point_mem with rfl | rfl | rfl
    · exact first_mem
    · exact second_mem
    · exact third_mem
  have seed_card : (indexedSeed firstIndex secondIndex thirdIndex).card = 3 := by
    simp [indexedSeed, first_ne_second, first_ne_third, second_ne_third]
  let extra := vertices \ indexedSeed firstIndex secondIndex thirdIndex
  have extra_card : extra.card = 4 := by
    change (vertices \ indexedSeed firstIndex secondIndex thirdIndex).card = 4
    rw [Finset.card_sdiff_of_subset seed_subset, vertices_card, seed_card]
  have vertices_candidate : reconstructionCandidateCheck vertices = true :=
    (reconstructionCandidateCheck_eq_true_iff vertices).mpr
      ⟨vertices_clique, vertices_zero⟩
  have extra_subset_pool : extra ⊆ extensionPool firstIndex secondIndex thirdIndex := by
    intro point point_mem
    have point_data := Finset.mem_sdiff.mp point_mem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ point, point_data.2, ?_⟩
    apply reconstructionCandidateCheck_mono (larger_check := vertices_candidate)
    intro candidate_point candidate_mem
    simp only [mem_insert] at candidate_mem
    rcases candidate_mem with rfl | seed_mem
    · exact point_data.1
    · exact seed_subset seed_mem
  let extraList := verticesInOrder extra
  have extraList_mem : extraList ∈
      (verticesInOrder (extensionPool firstIndex secondIndex thirdIndex)).sublistsLen 4 := by
    apply List.mem_sublistsLen.mpr
    constructor
    · exact verticesInOrder_sublist extra_subset_pool
    · simpa [extraList, verticesInOrder_length] using extra_card
  have union_eq : indexedSeed firstIndex secondIndex thirdIndex ∪ extraList.toFinset = vertices := by
    change indexedSeed firstIndex secondIndex thirdIndex ∪
      (verticesInOrder (vertices \ indexedSeed firstIndex secondIndex thirdIndex)).toFinset =
        vertices
    rw [verticesInOrder_toFinset]
    ext point
    constructor
    · intro point_mem
      rcases Finset.mem_union.mp point_mem with seed_mem | extra_mem
      · exact seed_subset seed_mem
      · exact (Finset.mem_sdiff.mp extra_mem).1
    · intro point_mem
      by_cases seed_mem : point ∈ indexedSeed firstIndex secondIndex thirdIndex
      · exact Finset.mem_union_left _ seed_mem
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨point_mem, seed_mem⟩)
  have seed_check := seed_extension_check_all_indices
    firstIndex secondIndex thirdIndex indices_distinct
      (reconstructionCandidateCheck_mono seed_subset vertices_candidate)
  have union_candidate : reconstructionCandidateCheck
      (indexedSeed firstIndex secondIndex thirdIndex ∪ extraList.toFinset) = true := by
    rw [union_eq]
    exact vertices_candidate
  have classified := seedExtensionCheck_sound firstIndex secondIndex thirdIndex seed_check
    extraList extraList_mem union_candidate
  rwa [union_eq] at classified

/-- The minimum-support hypergraph recovers exactly the 78 geometric passant-row supports. -/
theorem reconstructed_rows_eq_geometric_passant_rows :
    reconstructedRows semanticMinimumSupports =
      RelativeConicArcs.ConicPassantCode.rowSupports Incident := by
  apply reconstructedRows_eq_passantRows_of_sevenSet_transport semanticMinimumSupports
    geometric_rows_have_zero_triple_concurrence
  intro vertices vertices_card vertices_clique triple_zero
  apply admissible_seven_set_is_geometric_row vertices vertices_card vertices_clique
  intro first first_mem second second_mem third third_mem
    first_ne_second first_ne_third second_ne_third
  let triple : Finset InternalPoint := {first, second, third}
  have triple_mem : triple ∈ vertices.powersetCard 3 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro point point_mem
      simp only [triple, mem_insert, mem_singleton] at point_mem
      rcases point_mem with rfl | rfl | rfl
      · exact first_mem
      · exact second_mem
      · exact third_mem
    · simp [triple, first_ne_second, first_ne_third, second_ne_third]
  exact triple_zero triple triple_mem first (by simp [triple]) second (by simp [triple])
    third (by simp [triple]) first_ne_second first_ne_third second_ne_third

end PassantCodeQ13.MinimumWords.RowUniqueness
