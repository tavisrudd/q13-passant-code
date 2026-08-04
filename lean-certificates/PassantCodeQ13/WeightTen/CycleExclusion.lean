import PassantCodeQ13.WeightTen.Base

/-!
# Two-regular weight-ten configurations at a fixed internal point

The parity checks of the passant code are the passant incidence rows, so every codeword support
meets each passant in an even number of points.  An internal point of a conic over a field of odd
order lies on no tangent, so the join of two internal points is either a secant or a passant.  For a
ten-point support these two facts bound the secant degree of each support point by two, and a
support all of whose points have secant degree exactly two decomposes, at any fixed support point
`P`, into one point in each of the seven six-point passant fibres through `P` together with an
unordered pair of secant neighbours of `P`.

This module fixes the normalized internal point `(1,0,2)`, whose index in the coordinate list of
`RelativeConicArcs.PassantCodeQ13.Geometry` is zero, and provides the finite machinery excluding
every such configuration.  A configuration is *obstructed* when some passant carries three of its
points or some point of it has three secant neighbours inside it; neither is possible for a
ten-point codeword support in which every point has secant degree two.  The search prunes on a
cheap one-step test and the soundness theorems transport a successful prune to the obstruction
predicate on the completed configuration, so the conclusion covers every choice rather than the
enumeration order of any generator.

The fixed point is not transported to an arbitrary internal point here, and the reduction of an
arbitrary weight-ten support to this configuration shape is not carried out here.
-/

namespace PassantCodeQ13.WeightTen.CycleExclusion

open PassantCodeQ13.WeightTen

/-- An internal point index paired with the 78-bit mask of the passants through it.  The mask is a
natural number whose set bits are the indices of the incident normalized passant rows. -/
abbrev MarkedPoint : Type := Nat × Nat

/-- The internal point of the given index together with its passant incidence mask. -/
def marked (point : Nat) : MarkedPoint :=
  (point, columnSyndrome point)

/-- Two marked internal points are secantly joined when they are distinct and no passant contains
both, that is, when their incidence masks are disjoint. -/
def secantJoined (first second : MarkedPoint) : Bool :=
  first.1 != second.1 && (first.2 &&& second.2 == 0)

/-- The number of secant neighbours a marked point has inside a marked configuration. -/
def secantDegree (points : List MarkedPoint) (point : MarkedPoint) : Nat :=
  points.countP (secantJoined point)

/-- Some point of the configuration has at least three secant neighbours inside it. -/
def someSecantDegreeAtLeastThree (points : List MarkedPoint) : Bool :=
  points.any fun point => 3 ≤ secantDegree points point

/-- Some passant carries at least three points of the configuration.  Two distinct internal points
lie on at most one common passant, so a common set bit of three pairwise distinct incidence masks
is exactly a passant through all three points. -/
def someThreeOnPassant (points : List MarkedPoint) : Bool :=
  points.any fun first => points.any fun second => points.any fun third =>
    first.1 != second.1 && first.1 != third.1 && second.1 != third.1 &&
      (first.2 &&& second.2 &&& third.2 != 0)

/-- A marked configuration is obstructed when a passant carries three of its points or one of its
points has three secant neighbours inside it. -/
def obstructed (points : List MarkedPoint) : Bool :=
  someThreeOnPassant points || someSecantDegreeAtLeastThree points

/-- Three points on a common passant remain present after further points are added. -/
theorem someThreeOnPassant_append {points extra : List MarkedPoint}
    (present : someThreeOnPassant points = true) :
    someThreeOnPassant (points ++ extra) = true := by
  simp only [someThreeOnPassant, List.any_eq_true] at present ⊢
  obtain ⟨first, first_mem, second, second_mem, third, third_mem, checked⟩ := present
  exact ⟨first, List.mem_append_left _ first_mem, second, List.mem_append_left _ second_mem,
    third, List.mem_append_left _ third_mem, checked⟩

/-- A point with three secant neighbours keeps them after further points are added. -/
theorem someSecantDegreeAtLeastThree_append {points extra : List MarkedPoint}
    (present : someSecantDegreeAtLeastThree points = true) :
    someSecantDegreeAtLeastThree (points ++ extra) = true := by
  simp only [someSecantDegreeAtLeastThree, List.any_eq_true, decide_eq_true_eq] at present ⊢
  obtain ⟨point, point_mem, three_le⟩ := present
  refine ⟨point, List.mem_append_left _ point_mem, ?_⟩
  calc 3 ≤ secantDegree points point := three_le
    _ ≤ secantDegree points point + secantDegree extra point := Nat.le_add_right _ _
    _ = secantDegree (points ++ extra) point := by
        simp [secantDegree, List.countP_append]

/-- An obstructed configuration stays obstructed after further points are added. -/
theorem obstructed_append {points extra : List MarkedPoint}
    (present : obstructed points = true) :
    obstructed (points ++ extra) = true := by
  simp only [obstructed, Bool.or_eq_true] at present ⊢
  exact present.imp someThreeOnPassant_append someSecantDegreeAtLeastThree_append

/-- Adding a point places three points of the extended configuration on one passant.  This is the
one-step form of `someThreeOnPassant` used to prune the search. -/
def createsThreeOnPassant (chosen : List MarkedPoint) (point : MarkedPoint) : Bool :=
  chosen.any fun first => chosen.any fun second =>
    first.1 != second.1 && first.1 != point.1 && second.1 != point.1 &&
      (first.2 &&& second.2 &&& point.2 != 0)

/-- The one-step rejection test: adding the point either completes a passant triple or leaves some
point of the extended configuration with three secant neighbours. -/
def rejects (chosen : List MarkedPoint) (point : MarkedPoint) : Bool :=
  createsThreeOnPassant chosen point || someSecantDegreeAtLeastThree (chosen ++ [point])

/-- A completed passant triple obstructs the extended configuration. -/
theorem obstructed_of_createsThreeOnPassant {chosen : List MarkedPoint} {point : MarkedPoint}
    (created : createsThreeOnPassant chosen point = true) :
    obstructed (chosen ++ [point]) = true := by
  simp only [createsThreeOnPassant, List.any_eq_true] at created
  obtain ⟨first, first_mem, second, second_mem, checked⟩ := created
  simp only [obstructed, Bool.or_eq_true]
  refine Or.inl ?_
  simp only [someThreeOnPassant, List.any_eq_true]
  exact ⟨first, List.mem_append_left _ first_mem, second, List.mem_append_left _ second_mem,
    point, List.mem_append_right _ (List.mem_singleton_self _), checked⟩

/-- A successful one-step rejection obstructs the extended configuration. -/
theorem obstructed_of_rejects {chosen : List MarkedPoint} {point : MarkedPoint}
    (rejected : rejects chosen point = true) :
    obstructed (chosen ++ [point]) = true := by
  simp only [rejects, Bool.or_eq_true] at rejected
  rcases rejected with created | degree_three
  · exact obstructed_of_createsThreeOnPassant created
  · simp only [obstructed, Bool.or_eq_true]
    exact Or.inr degree_three

/-- A list selects one marked point from each supplied list of options, in order. -/
inductive Selection : List (List MarkedPoint) → List MarkedPoint → Prop
  | nil : Selection [] []
  | cons {options remaining choice tail} :
      choice ∈ options → Selection remaining tail →
        Selection (options :: remaining) (choice :: tail)

/-- Every completion of the chosen points by one option from each remaining list is obstructed.  The
search rejects a prefix as soon as the one-step test fires, so a `true` value covers the whole
Cartesian domain of completions. -/
def everyCompletionObstructed (chosen : List MarkedPoint) : List (List MarkedPoint) → Bool
  | [] => obstructed chosen
  | options :: remaining =>
      options.all fun point =>
        if rejects chosen point then true
        else everyCompletionObstructed (chosen ++ [point]) remaining

/-- A successful search obstructs every selection, independently of any enumeration order. -/
theorem obstructed_of_everyCompletionObstructed {options : List (List MarkedPoint)}
    {path : List MarkedPoint} (selection : Selection options path) :
    ∀ {chosen : List MarkedPoint}, everyCompletionObstructed chosen options = true →
      obstructed (chosen ++ path) = true := by
  induction selection with
  | nil =>
      intro chosen checked
      simpa [everyCompletionObstructed] using checked
  | @cons options remaining choice tail choice_mem _ induction =>
      intro chosen checked
      have step : (if rejects chosen choice then true
          else everyCompletionObstructed (chosen ++ [choice]) remaining) = true :=
        (List.all_eq_true.mp checked) choice choice_mem
      have regroup : chosen ++ choice :: tail = (chosen ++ [choice]) ++ tail := by
        simp
      rw [regroup]
      by_cases rejected : rejects chosen choice = true
      · exact obstructed_append (obstructed_of_rejects rejected)
      · rw [if_neg (by simpa using rejected)] at step
        exact induction step

/-- The seven six-point passant fibres through the base point, with incidence masks. -/
def markedFibres : List (List MarkedPoint) :=
  fibres.map (List.map marked)

/-- The base point `(1,0,2)` together with a marked secant pair. -/
def markedStart (pair : List Nat) : List MarkedPoint :=
  marked 0 :: pair.map marked

/-- Every configuration built from the base point, the given secant pair, and one point in each
passant fibre through the base point is obstructed. -/
def pairObstructed (pair : List Nat) : Bool :=
  everyCompletionObstructed (markedStart pair) markedFibres

/-- Unordered pairs of secant neighbours of the base point whose lower endpoint has coordinate
index in the given class modulo seven. -/
def secantPairShard (residue : Nat) : List (List Nat) :=
  (secantNeighbors.sublistsLen 2).filter fun pair => pair.headD 0 % 7 == residue

/-- Every configuration over one residue shard of secant pairs is obstructed. -/
def shardObstructed (residue : Nat) : Bool :=
  (secantPairShard residue).all pairObstructed

/-- The seven residue shards cover every unordered pair of secant neighbours. -/
theorem pairObstructed_of_shards
    (shards : ∀ residue, residue < 7 → shardObstructed residue = true)
    {pair : List Nat} (pair_mem : pair ∈ secantNeighbors.sublistsLen 2) :
    pairObstructed pair = true := by
  have residue_lt : pair.headD 0 % 7 < 7 := Nat.mod_lt _ (by decide)
  have shard_mem : pair ∈ secantPairShard (pair.headD 0 % 7) := by
    simp [secantPairShard, List.mem_filter, pair_mem]
  exact (List.all_eq_true.mp (shards _ residue_lt)) pair shard_mem

/-- Given the seven shard checks, every configuration consisting of the base point, an unordered
pair of its secant neighbours, and one point in each of the seven passant fibres through it has a
passant carrying three of its points or a point with three secant neighbours.  Hence no such
configuration is the support of a codeword all of whose points have secant degree two. -/
theorem obstructed_of_shards
    (shards : ∀ residue, residue < 7 → shardObstructed residue = true)
    {pair : List Nat} (pair_mem : pair ∈ secantNeighbors.sublistsLen 2)
    {path : List MarkedPoint} (selection : Selection markedFibres path) :
    obstructed (markedStart pair ++ path) = true :=
  obstructed_of_everyCompletionObstructed selection (pairObstructed_of_shards shards pair_mem)

end PassantCodeQ13.WeightTen.CycleExclusion
