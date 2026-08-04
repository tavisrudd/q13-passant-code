import PassantCodeQ13.MinimumWords.Reconstruction
import RelativeConicArcs.PassantCodeQ13.Reconstruction

/-!
# Indexed supports for passant-row reconstruction

The four projective minimum-word orbits are decoded from their 78-bit representation into the
semantic internal-point type.  The row-uniqueness certificate is partitioned by the first point's
index modulo seven.  For each three-point seed, it constructs the at-most-ten-point pool of
one-point admissible extensions and checks every four-subset of that pool.  This covers all
admissible seven-sets without enumerating the ambient `78 choose 7` domain.
-/

namespace PassantCodeQ13.MinimumWords.RowUniqueness

open Finset
open RelativeConicArcs.PassantCodeQ13

/-- Decode a 78-bit support into the normalized semantic internal-point type. -/
def decodedSupport (support : Nat) : Finset InternalPoint :=
  (Finset.univ.filter fun index : Fin 78 => support.testBit index.1).image internalPointAt

/-- Bit membership in an encoded support is semantic membership after decoding. -/
theorem mem_decodedSupport (support : Nat) (index : Fin 78) :
    internalPointAt index ∈ decodedSupport support ↔ support.testBit index.1 = true := by
  constructor
  · intro membership
    obtain ⟨sourceIndex, source_mem, equality⟩ := Finset.mem_image.mp membership
    have source_eq : sourceIndex = index := internalPointAt_bijective.injective equality
    subst sourceIndex
    exact (Finset.mem_filter.mp source_mem).2
  · intro bit
    exact Finset.mem_image.mpr
      ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bit⟩, rfl⟩

/-- The semantic support hypergraph formed by the four displayed projective orbits. -/
def semanticMinimumSupports : Finset (Finset InternalPoint) :=
  minimumSupportCodes.toFinset.image decodedSupport

/-- Pairwise check that decoding is injective on the four-orbit support list. -/
def decodedSupportInjectivityCheck : Bool :=
  minimumSupportCodes.all fun first => minimumSupportCodes.all fun second =>
    first == second || !(decodedSupport first == decodedSupport second)

/-- A successful pairwise check proves injectivity on the encoded minimum-support family. -/
theorem decodedSupport_injOn_of_check (check : decodedSupportInjectivityCheck = true) :
    Set.InjOn decodedSupport minimumSupportCodes.toFinset := by
  intro first first_mem second second_mem decoded_eq
  have first_list_mem : first ∈ minimumSupportCodes := List.mem_toFinset.mp first_mem
  have second_list_mem : second ∈ minimumSupportCodes := List.mem_toFinset.mp second_mem
  have checked := (List.all_eq_true.mp
    (List.all_eq_true.mp check first first_list_mem)) second second_list_mem
  simp [decoded_eq] at checked
  exact checked

/-- The semantic internal points in the fixed displayed order. -/
def internalPointOrder : List InternalPoint :=
  List.ofFn internalPointAt

/-- The displayed semantic point order has no repetitions. -/
theorem internalPointOrder_nodup : internalPointOrder.Nodup := by
  rw [internalPointOrder, List.nodup_ofFn]
  exact internalPointAt_bijective.injective

/-- Restrict the displayed point order to a finite vertex set. -/
def verticesInOrder (vertices : Finset InternalPoint) : List InternalPoint :=
  internalPointOrder.filter fun point => point ∈ vertices

/-- Restricting the displayed order recovers the original finite set. -/
theorem verticesInOrder_toFinset (vertices : Finset InternalPoint) :
    (verticesInOrder vertices).toFinset = vertices := by
  ext point
  have point_mem : point ∈ internalPointOrder := by
    rw [internalPointOrder, List.mem_ofFn']
    exact internalPointAt_bijective.surjective point
  simp [verticesInOrder, point_mem]

/-- Restriction of the displayed order has no repetitions. -/
theorem verticesInOrder_nodup (vertices : Finset InternalPoint) :
    (verticesInOrder vertices).Nodup :=
  internalPointOrder_nodup.filter _

/-- The restricted displayed list has the cardinality of its finite set. -/
theorem verticesInOrder_length (vertices : Finset InternalPoint) :
    (verticesInOrder vertices).length = vertices.card := by
  have card_identity := List.card_toFinset (l := verticesInOrder vertices)
  rw [List.dedup_eq_self.mpr (verticesInOrder_nodup vertices),
    verticesInOrder_toFinset] at card_identity
  exact card_identity.symm

/-- Inclusion of finite vertex sets gives a sublist relation in the common displayed order. -/
theorem verticesInOrder_sublist {smaller larger : Finset InternalPoint}
    (subset : smaller ⊆ larger) :
    List.Sublist (verticesInOrder smaller) (verticesInOrder larger) := by
  unfold verticesInOrder
  induction internalPointOrder with
  | nil => simp
  | cons point points induction_hypothesis =>
      by_cases point_mem_smaller : point ∈ smaller
      · have point_mem_larger := subset point_mem_smaller
        simp [point_mem_smaller, point_mem_larger, induction_hypothesis]
      · by_cases point_mem_larger : point ∈ larger
        · simp [point_mem_smaller, point_mem_larger]
          exact induction_hypothesis.cons point
        · simp [point_mem_smaller, point_mem_larger, induction_hypothesis]

@[simp] theorem mem_verticesInOrder (point : InternalPoint) (vertices : Finset InternalPoint) :
    point ∈ verticesInOrder vertices ↔ point ∈ vertices := by
  rw [← List.mem_toFinset, verticesInOrder_toFinset]

/-- Displayed index of a semantic internal point. -/
def internalPointIndex (point : InternalPoint) : Nat :=
  internalPointOrder.idxOf point

/-- The displayed semantic point at an index has that same executable index. -/
theorem internalPointIndex_internalPointAt (index : Fin 78) :
    internalPointIndex (internalPointAt index) = index.1 := by
  let listIndex : Fin internalPointOrder.length :=
    Fin.cast (by simp [internalPointOrder]) index
  have point_eq : internalPointOrder.get listIndex = internalPointAt index := by
    change (List.ofFn internalPointAt).get listIndex = internalPointAt index
    rw [List.get_ofFn]
    apply congrArg internalPointAt
    apply Fin.ext
    rfl
  have indexed := List.get_idxOf internalPointOrder_nodup listIndex
  rw [point_eq] at indexed
  simpa [listIndex, internalPointIndex] using indexed

/-- Executable passant-join test through displayed point indices. -/
def indexedPassantJoin (first second : InternalPoint) : Bool :=
  hasPassantJoin (internalPointIndex first) (internalPointIndex second)

/-- Executable minimum-layer triple concurrence through displayed point indices. -/
def indexedTripleConcurrence (first second third : InternalPoint) : Nat :=
  tripleConcurrenceIn minimumSupportCodes (internalPointIndex first)
    (internalPointIndex second) (internalPointIndex third)

/-- Executable intrinsic test against an explicitly supplied encoded support family. -/
def reconstructionCandidateCheckWith (supports : List Nat)
    (vertices : Finset InternalPoint) : Bool :=
  let pairCheck := (verticesInOrder vertices).all fun first =>
      (verticesInOrder vertices).all fun second =>
        if first == second then true else indexedPassantJoin first second
  if pairCheck then
    supports.all fun support =>
      (verticesInOrder vertices).countP
        (fun point => support.testBit (internalPointIndex point)) ≤ 2
  else false

/-- Executable intrinsic test for a passant clique with zero concurrence on distinct triples. -/
def reconstructionCandidateCheck (vertices : Finset InternalPoint) : Bool :=
  reconstructionCandidateCheckWith minimumSupportCodes vertices

/-- The three-point seed selected by displayed internal-point indices. -/
def indexedSeed (firstIndex secondIndex thirdIndex : Fin 78) : Finset InternalPoint :=
  {internalPointAt firstIndex, internalPointAt secondIndex, internalPointAt thirdIndex}

/-- Points that extend a seed relative to an explicitly supplied encoded support family. -/
def extensionPoolWith (supports : List Nat) (firstIndex secondIndex thirdIndex : Fin 78) :
    Finset InternalPoint :=
  Finset.univ.filter fun point =>
    point ∉ indexedSeed firstIndex secondIndex thirdIndex ∧
      reconstructionCandidateCheckWith supports
        (insert point (indexedSeed firstIndex secondIndex thirdIndex)) = true

/-- Points that extend a seed to an intrinsic four-point candidate. -/
def extensionPool (firstIndex secondIndex thirdIndex : Fin 78) : Finset InternalPoint :=
  extensionPoolWith minimumSupportCodes firstIndex secondIndex thirdIndex

/-- Check every four-point extension against an explicitly supplied encoded support family. -/
def seedExtensionCheckWith (supports : List Nat)
    (firstIndex secondIndex thirdIndex : Fin 78) : Bool :=
  ((verticesInOrder
    (extensionPoolWith supports firstIndex secondIndex thirdIndex)).sublistsLen 4).all
      fun extraList =>
    let extra := extraList.toFinset
    let vertices := indexedSeed firstIndex secondIndex thirdIndex ∪ extra
    if reconstructionCandidateCheckWith supports vertices then
      decide (vertices ∈ RelativeConicArcs.ConicPassantCode.rowSupports Incident)
    else true

/-- Check every four-point extension of an indexed seed that can form an admissible seven-set. -/
def seedExtensionCheck (firstIndex secondIndex thirdIndex : Fin 78) : Bool :=
  seedExtensionCheckWith minimumSupportCodes firstIndex secondIndex thirdIndex

/-- Equal displayed seed sets give equal extension checks against the same support family. -/
theorem seedExtensionCheckWith_eq_of_seed_eq (supports : List Nat)
    (firstIndex secondIndex thirdIndex reorderedFirst reorderedSecond reorderedThird : Fin 78)
    (seed_eq : indexedSeed firstIndex secondIndex thirdIndex =
      indexedSeed reorderedFirst reorderedSecond reorderedThird) :
    seedExtensionCheckWith supports firstIndex secondIndex thirdIndex =
      seedExtensionCheckWith supports reorderedFirst reorderedSecond reorderedThird := by
  simp only [seedExtensionCheckWith, extensionPoolWith, seed_eq]

/-- Permuting three displayed seed indices does not change the public extension check. -/
theorem seedExtensionCheck_eq_of_seed_eq
    (firstIndex secondIndex thirdIndex reorderedFirst reorderedSecond reorderedThird : Fin 78)
    (seed_eq : indexedSeed firstIndex secondIndex thirdIndex =
      indexedSeed reorderedFirst reorderedSecond reorderedThird) :
    seedExtensionCheck firstIndex secondIndex thirdIndex =
      seedExtensionCheck reorderedFirst reorderedSecond reorderedThird :=
  seedExtensionCheckWith_eq_of_seed_eq minimumSupportCodes firstIndex secondIndex thirdIndex
    reorderedFirst reorderedSecond reorderedThird seed_eq

/-- The seed-extension check for all second and third indices at one first index. -/
def rowExtensionCheckAt (firstIndex : Fin 78) : Bool :=
  let supports := minimumSupportCodes
  (List.finRange 78).all fun secondIndex =>
    (List.finRange 78).all fun thirdIndex =>
      if decide (firstIndex = secondIndex ∨ firstIndex = thirdIndex ∨
        secondIndex = thirdIndex ∨ secondIndex.1 < firstIndex.1 ∨
          thirdIndex.1 < secondIndex.1) then true
      else if reconstructionCandidateCheckWith supports
        (indexedSeed firstIndex secondIndex thirdIndex) then
          seedExtensionCheckWith supports firstIndex secondIndex thirdIndex
      else true

/-- A successful seed-extension check classifies each admissible four-extension as a row. -/
theorem seedExtensionCheck_sound
    (firstIndex secondIndex thirdIndex : Fin 78)
    (check : seedExtensionCheck firstIndex secondIndex thirdIndex = true)
    (extraList : List InternalPoint)
    (extra_mem : extraList ∈
      (verticesInOrder (extensionPool firstIndex secondIndex thirdIndex)).sublistsLen 4)
    (candidate : reconstructionCandidateCheck
      (indexedSeed firstIndex secondIndex thirdIndex ∪ extraList.toFinset) = true) :
    indexedSeed firstIndex secondIndex thirdIndex ∪ extraList.toFinset ∈
      RelativeConicArcs.ConicPassantCode.rowSupports Incident := by
  have classified := (List.all_eq_true.mp check) extraList extra_mem
  have candidate_with : reconstructionCandidateCheckWith minimumSupportCodes
      (indexedSeed firstIndex secondIndex thirdIndex ∪ extraList.toFinset) = true := by
    simpa [reconstructionCandidateCheck] using candidate
  simpa [candidate_with] using classified

/-- Extract one indexed seed check from the complete first-index check. -/
theorem seedExtensionCheck_of_rowExtensionCheckAt
    (firstIndex secondIndex thirdIndex : Fin 78)
    (indices_distinct : firstIndex ≠ secondIndex ∧ firstIndex ≠ thirdIndex ∧
      secondIndex ≠ thirdIndex)
    (first_lt_second : firstIndex.1 < secondIndex.1)
    (second_lt_third : secondIndex.1 < thirdIndex.1)
    (seed_candidate : reconstructionCandidateCheck
      (indexedSeed firstIndex secondIndex thirdIndex) = true)
    (check : rowExtensionCheckAt firstIndex = true) :
    seedExtensionCheck firstIndex secondIndex thirdIndex = true := by
  have second_check := (List.all_eq_true.mp check) secondIndex (by simp)
  have third_check := (List.all_eq_true.mp second_check) thirdIndex (by simp)
  have seed_candidate_with : reconstructionCandidateCheckWith minimumSupportCodes
      (indexedSeed firstIndex secondIndex thirdIndex) = true := by
    simpa [reconstructionCandidateCheck] using seed_candidate
  simpa [seedExtensionCheck, indices_distinct.1, indices_distinct.2.1,
    indices_distinct.2.2, Nat.not_lt.mpr (Nat.le_of_lt first_lt_second),
    Nat.not_lt.mpr (Nat.le_of_lt second_lt_third), seed_candidate_with] using third_check

/-- Every geometric passant row has zero concurrence on its triples in the decoded minimum layer. -/
def GeometricRowsHaveZeroTripleConcurrence : Prop :=
  ∀ line : PassantLine, ∀ first second third : InternalPoint,
    Incident line first → Incident line second → Incident line third →
      first ≠ second → first ≠ third → second ≠ third →
      RelativeConicArcs.ConicPassantCode.tripleConcurrence
        semanticMinimumSupports first second third = 0

end PassantCodeQ13.MinimumWords.RowUniqueness
