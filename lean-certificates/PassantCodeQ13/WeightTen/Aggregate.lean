import PassantCodeQ13.WeightTen.IsolatedProfile.Fibre0
import PassantCodeQ13.WeightTen.IsolatedProfile.Fibre1
import PassantCodeQ13.WeightTen.IsolatedProfile.Fibre2
import PassantCodeQ13.WeightTen.IsolatedProfile.Fibre3
import PassantCodeQ13.WeightTen.IsolatedProfile.Fibre4
import PassantCodeQ13.WeightTen.IsolatedProfile.Fibre5
import PassantCodeQ13.WeightTen.IsolatedProfile.Fibre6
import PassantCodeQ13.WeightTen.CycleProfile.Residue0
import PassantCodeQ13.WeightTen.CycleProfile.Residue1
import PassantCodeQ13.WeightTen.CycleProfile.Residue2
import PassantCodeQ13.WeightTen.CycleProfile.Residue3
import PassantCodeQ13.WeightTen.CycleProfile.Residue4
import PassantCodeQ13.WeightTen.CycleProfile.Residue5
import PassantCodeQ13.WeightTen.CycleProfile.Residue6

/-!
# Aggregate q=13 weight-ten certificate

The local partition is checked from the normalized conic incidence relation.  The isolated-profile
leaves cover each possible distinguished passant fibre.  The cycle-profile leaves partition all
unordered pairs of the thirty-five secant neighbors by the first endpoint's coordinate index
modulo seven.  The aggregate joins the fourteen independently elaborated native terminals.
-/

namespace PassantCodeQ13.WeightTen

/-- The fixed-base incidence partition consists of seven six-point passant fibres and thirty-five
secant neighbors. -/
theorem local_partition : localPartitionCheck = true := by
  native_decide

/-- Every isolated-profile shard has disjoint left and right syndrome images. -/
theorem all_isolated_profiles_disjoint :
    isolatedProfileCheck 0 = true ∧ isolatedProfileCheck 1 = true ∧
      isolatedProfileCheck 2 = true ∧ isolatedProfileCheck 3 = true ∧
      isolatedProfileCheck 4 = true ∧ isolatedProfileCheck 5 = true ∧
      isolatedProfileCheck 6 = true :=
  ⟨IsolatedProfile.fibre0_syndrome_disjoint, IsolatedProfile.fibre1_syndrome_disjoint,
    IsolatedProfile.fibre2_syndrome_disjoint, IsolatedProfile.fibre3_syndrome_disjoint,
    IsolatedProfile.fibre4_syndrome_disjoint, IsolatedProfile.fibre5_syndrome_disjoint,
    IsolatedProfile.fibre6_syndrome_disjoint⟩

/-- Every cycle-profile residue shard has disjoint left and right syndrome images. -/
theorem all_cycle_profiles_disjoint :
    cycleProfileCheck 0 = true ∧ cycleProfileCheck 1 = true ∧
      cycleProfileCheck 2 = true ∧ cycleProfileCheck 3 = true ∧
      cycleProfileCheck 4 = true ∧ cycleProfileCheck 5 = true ∧
      cycleProfileCheck 6 = true :=
  ⟨CycleProfile.residue0_syndrome_disjoint, CycleProfile.residue1_syndrome_disjoint,
    CycleProfile.residue2_syndrome_disjoint, CycleProfile.residue3_syndrome_disjoint,
    CycleProfile.residue4_syndrome_disjoint, CycleProfile.residue5_syndrome_disjoint,
    CycleProfile.residue6_syndrome_disjoint⟩

/-- Encode an unordered pair of point indices for a canonical multiset comparison. -/
def encodePair : List Nat → Nat
  | [first, second] => 78 * first + second
  | _ => 0

/-- The seven residue shards contain exactly the unordered pairs of secant neighbors, with the same
multiplicity. -/
theorem cycle_pair_partition :
    (((List.range 7).flatMap cyclePairs).map encodePair).mergeSort =
      ((secantNeighbors.sublistsLen 2).map encodePair).mergeSort := by
  native_decide

end PassantCodeQ13.WeightTen
