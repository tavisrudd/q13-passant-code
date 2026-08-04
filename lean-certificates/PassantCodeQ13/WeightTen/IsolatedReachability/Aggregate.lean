import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre0
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre1
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre2
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre3
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre4
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre6

/-!
# Aggregate isolated-profile syndrome exclusion

At the fixed internal point, an isolated weight-ten profile chooses one syndrome increment from
each of three ordinary passant fibres on the left.  On the right it chooses the base column, one
three-point increment in a distinguished passant fibre, and one increment from each remaining
ordinary fibre.  The seven possible distinguished fibres exhaust this profile.

Each imported leaf checks explicit transition layers by kernel reduction.  Its soundness theorem
then applies the checked coverage to every member of the corresponding Cartesian choice domain.
-/

namespace PassantCodeQ13.WeightTen.IsolatedReachability

open PassantCodeQ13.WeightTen
open PassantCodeQ13.WeightTen.Reachability

/-- Complete Cartesian syndrome exclusion for the isolated profile with distinguished fibre
`special`. -/
def ProfileExcluded (special : Nat) : Prop :=
  ∀ {leftPath rightPath : List Nat},
    ChoicePath (isolatedLeftOptions special) leftPath →
    ChoicePath (isolatedRightOptions special) rightPath →
    leftPath.foldl (fun state increment => state ^^^ increment) 0 ≠
      rightPath.foldl (fun state increment => state ^^^ increment) 0

/-- Every one of the seven distinguished-fibre cases excludes equality between the two syndrome
halves for every complete Cartesian choice. -/
theorem all_profiles_excluded :
    ProfileExcluded 0 ∧ ProfileExcluded 1 ∧ ProfileExcluded 2 ∧ ProfileExcluded 3 ∧
      ProfileExcluded 4 ∧ ProfileExcluded 5 ∧ ProfileExcluded 6 := by
  exact ⟨Fibre0.no_equal_cartesian_syndromes, Fibre1.no_equal_cartesian_syndromes,
    Fibre2.no_equal_cartesian_syndromes, Fibre3.no_equal_cartesian_syndromes,
    Fibre4.no_equal_cartesian_syndromes, Fibre5.no_equal_cartesian_syndromes,
    Fibre6.no_equal_cartesian_syndromes⟩

end PassantCodeQ13.WeightTen.IsolatedReachability
