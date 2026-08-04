import Mathlib.Data.List.GetD
import PassantCodeQ13.WeightTen.Base
import RelativeConicArcs.PassantCodeQ13.WeightTen

/-!
# The base pencil in both the indexed and the subtype presentation

The finite weight-ten certificates address internal points and passant lines by their position in
the normalized coordinate lists of `RelativeConicArcs.PassantCodeQ13.Geometry` and record incidence
in `78`-bit masks.  The pencil-profile theorem
`RelativeConicArcs.PassantCodeQ13.WeightTen.arbitrary_weightTen_word_has_pencil_profile` instead
quantifies over the subtypes `InternalPoint` and `PassantLine`.  This module states the dictionary
between the two presentations at the internal point `(1,0,2)`, which is the point of index zero and
the base point of the certificates.

Nothing here is a finite search.  The executable incidence test `incidentAt` and the incidence
relation `Incident` are the same field equation applied to the same normalized triples, so the
dictionary follows from the defining equations of the indexed lists.  On that basis the indexed
passant pencil through the base point, the fibre of one pencil line, and the list of secant
neighbours are identified with their semantic counterparts: a pencil line is a passant line through
the base point, its fibre is the set of internal points on it other than the base point, and a
secant neighbour is an internal point other than the base point lying on no common passant with it.
-/

namespace PassantCodeQ13.WeightTen.PencilTransport

open RelativeConicArcs.PassantCodeQ13
open PassantCodeQ13.WeightTen

/-- The coordinate triple of the internal point at a displayed index. -/
theorem internalPointAt_val (index : Fin 78) :
    (internalPointAt index).1 = internalAt index.1 := by
  have bound : index.1 < internalCoordinateList.length := by
    rw [internalCoordinateList_length]
    exact index.2
  simp [internalPointAt, internalAt, List.getElem?_eq_getElem bound]

/-- The coordinate triple of the passant line at a displayed index. -/
theorem passantLineAt_val (index : Fin 78) :
    (passantLineAt index).1 = passantAt index.1 := by
  have bound : index.1 < passantCoordinateList.length := by
    rw [passantCoordinateList_length]
    exact index.2
  simp [passantLineAt, passantAt, List.getElem?_eq_getElem bound]

/-- The executable incidence test on displayed indices is the incidence relation on the
corresponding normalized point and line. -/
theorem incidentAt_iff (line point : Fin 78) :
    incidentAt line.1 point.1 = true ↔ Incident (passantLineAt line) (internalPointAt point) := by
  simp [incidentAt, Incident, passantLineAt_val, internalPointAt_val]

/-- The internal point `(1,0,2)` of index zero, at which the weight-ten certificates are anchored. -/
def basePoint : InternalPoint := internalPointAt 0

/-- Every index listed in the base pencil is a displayed passant index. -/
theorem lt_of_mem_linesThroughBase {line : Nat} (mem : line ∈ linesThroughBase) : line < 78 :=
  List.mem_range.mp (List.mem_filter.mp mem).1

/-- The indexed base pencil consists exactly of the passant lines through the base point. -/
theorem mem_linesThroughBase (line : Fin 78) :
    line.1 ∈ linesThroughBase ↔ Incident (passantLineAt line) basePoint := by
  rw [linesThroughBase, List.mem_filter]
  constructor
  · intro data
    exact (incidentAt_iff line 0).mp data.2
  · intro incident
    exact ⟨List.mem_range.mpr line.2, (incidentAt_iff line 0).mpr incident⟩

/-- The internal points other than the base point on the passant line of the given index. -/
def fibreOf (line : Nat) : List Nat :=
  (List.range 78).filter fun point => point != 0 && incidentAt line point

/-- The fibre lists of the certificates are the fibres of the lines of the base pencil. -/
theorem fibres_eq_map : fibres = linesThroughBase.map fibreOf := rfl

/-- Every index listed in a fibre is a displayed internal-point index. -/
theorem lt_of_mem_fibreOf {line point : Nat} (mem : point ∈ fibreOf line) : point < 78 :=
  List.mem_range.mp (List.mem_filter.mp mem).1

/-- The fibre of a pencil line consists exactly of the internal points on it other than the base
point. -/
theorem mem_fibreOf (line point : Fin 78) :
    point.1 ∈ fibreOf line.1 ↔
      point ≠ 0 ∧ Incident (passantLineAt line) (internalPointAt point) := by
  rw [fibreOf, List.mem_filter]
  constructor
  · intro data
    have checked := Bool.and_eq_true .. |>.mp data.2
    refine ⟨?_, (incidentAt_iff line point).mp checked.2⟩
    intro point_eq
    exact absurd (congrArg Fin.val point_eq) (by simpa using checked.1)
  · intro data
    refine ⟨List.mem_range.mpr point.2, ?_⟩
    refine Bool.and_eq_true .. |>.mpr ⟨?_, (incidentAt_iff line point).mpr data.2⟩
    simpa using fun value_eq => data.1 (Fin.ext value_eq)

/-- An internal point occurs in some fibre exactly when it differs from the base point and lies with
it on a common passant. -/
theorem mem_fibres_flatten (point : Fin 78) :
    point.1 ∈ fibres.flatten ↔
      point ≠ 0 ∧ WeightEight.PassantJoin basePoint (internalPointAt point) := by
  rw [fibres_eq_map, List.mem_flatten]
  constructor
  · rintro ⟨fibre, fibre_mem, point_mem⟩
    obtain ⟨line, line_mem, rfl⟩ := List.mem_map.mp fibre_mem
    have line_lt : line < 78 := lt_of_mem_linesThroughBase line_mem
    have indexed := (mem_fibreOf ⟨line, line_lt⟩ point).mp point_mem
    refine ⟨indexed.1, ⟨passantLineAt ⟨line, line_lt⟩, ?_, indexed.2⟩⟩
    exact (mem_linesThroughBase ⟨line, line_lt⟩).mp line_mem
  · rintro ⟨distinct, line, base_incident, point_incident⟩
    obtain ⟨index, rfl⟩ := passantLineAt_bijective.surjective line
    refine ⟨fibreOf index.1, ?_, (mem_fibreOf index point).mpr ⟨distinct, point_incident⟩⟩
    exact List.mem_map.mpr ⟨index.1, (mem_linesThroughBase index).mpr base_incident, rfl⟩

/-- The secant neighbours of the certificates are exactly the internal points other than the base
point that lie on no common passant with it. -/
theorem mem_secantNeighbors (point : Fin 78) :
    point.1 ∈ secantNeighbors ↔
      point ≠ 0 ∧ ¬WeightEight.PassantJoin basePoint (internalPointAt point) := by
  rw [secantNeighbors, List.mem_filter]
  constructor
  · intro data
    have checked := Bool.and_eq_true .. |>.mp data.2
    have distinct : point ≠ 0 := by
      intro point_eq
      exact absurd (congrArg Fin.val point_eq) (by simpa using checked.1)
    refine ⟨distinct, ?_⟩
    intro join
    have flattened := (mem_fibres_flatten point).mpr ⟨distinct, join⟩
    have contained : fibres.flatten.contains point.1 = true :=
      List.contains_iff_mem.mpr flattened
    rw [contained] at checked
    exact absurd checked.2 (by decide)
  · intro data
    refine ⟨List.mem_range.mpr point.2, ?_⟩
    refine Bool.and_eq_true .. |>.mpr ⟨?_, ?_⟩
    · simpa using fun value_eq => data.1 (Fin.ext value_eq)
    · have absent : fibres.flatten.contains point.1 = false := by
        apply Bool.eq_false_iff.mpr
        intro contained
        exact data.2 ((mem_fibres_flatten point).mp (List.contains_iff_mem.mp contained)).2
      rw [absent]
      rfl

/-- Every index listed as a secant neighbour is a displayed internal-point index. -/
theorem lt_of_mem_secantNeighbors {point : Nat} (mem : point ∈ secantNeighbors) : point < 78 :=
  List.mem_range.mp (List.mem_filter.mp mem).1

end PassantCodeQ13.WeightTen.PencilTransport
