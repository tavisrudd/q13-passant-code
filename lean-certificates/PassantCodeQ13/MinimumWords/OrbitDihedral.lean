import PassantCodeQ13.MinimumWords.OrbitDihedralA
import PassantCodeQ13.MinimumWords.OrbitDihedralB
import PassantCodeQ13.MinimumWords.OrbitDihedralC

/-! # Aggregate for the three dihedral minimum-word orbits -/

namespace PassantCodeQ13.MinimumWords

/-- The three dihedral orbits are pairwise disjoint. -/
theorem dihedral_orbits_pairwise_disjoint :
    (supportOrbit representativeDihedralA).all
        (fun support => !(supportOrbit representativeDihedralB).contains support) = true ∧
      (supportOrbit representativeDihedralA).all
        (fun support => !(supportOrbit representativeDihedralC).contains support) = true ∧
      (supportOrbit representativeDihedralB).all
        (fun support => !(supportOrbit representativeDihedralC).contains support) = true := by
  native_decide

end PassantCodeQ13.MinimumWords
