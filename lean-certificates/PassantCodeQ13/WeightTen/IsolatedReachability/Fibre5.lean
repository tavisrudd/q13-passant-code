import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.LeftOptions
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.RightOptions
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.LeftOrdinaryA
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.LeftOrdinaryB
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.LeftOrdinaryC
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.Base
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.DistinguishedTriple
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.RightOrdinaryA
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.RightOrdinaryB
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.RightOrdinaryC
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.TerminalDisjoint.FirstThird
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.TerminalDisjoint.MiddleThird
import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5.TerminalDisjoint.LastThird

/-!
# Reachability certificate for an isolated weight-ten fibre

The generated state lists contain every syndrome reached by the complete Cartesian domains on the
two sides of the meet-in-the-middle decomposition for distinguished passant fibre 5.
Independent kernel-reduced modules check each mathematical transition and terminal disjointness.
The terminal theorem therefore excludes equality for arbitrary choices, rather than only for the
generated enumeration order.
-/

namespace PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5

open PassantCodeQ13.WeightTen
open PassantCodeQ13.WeightTen.Reachability
open PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre5

/-- The generated left layers cover all three ordinary-fibre choices. -/
theorem left_chain : chainCheck [0] (isolatedLeftOptions 5) leftLayers = true := by
  rw [LeftOptions.checked]
  exact chainCheck_cons_of_transitionCheck LeftOrdinaryA.transition_checked
    (chainCheck_cons_of_transitionCheck LeftOrdinaryB.transition_checked
      (chainCheck_cons_of_transitionCheck LeftOrdinaryC.transition_checked
        (chainCheck_nil leftOrdinaryC)))

/-- The generated right layers cover the base, three-point, and three remaining fibres. -/
theorem right_chain : chainCheck [0] (isolatedRightOptions 5) rightLayers = true := by
  rw [RightOptions.checked]
  exact chainCheck_cons_of_transitionCheck Base.transition_checked
    (chainCheck_cons_of_transitionCheck DistinguishedTriple.transition_checked
      (chainCheck_cons_of_transitionCheck RightOrdinaryA.transition_checked
        (chainCheck_cons_of_transitionCheck RightOrdinaryB.transition_checked
          (chainCheck_cons_of_transitionCheck RightOrdinaryC.transition_checked
            (chainCheck_nil rightOrdinaryC)))))

/-- The two terminal reachable-state lists are disjoint. -/
theorem terminal_disjoint :
    disjointCheck (terminalStates [0] leftLayers) (terminalStates [0] rightLayers) = true := by
  have first_two := disjointCheck_append TerminalDisjoint.FirstThird.checked
    TerminalDisjoint.MiddleThird.checked
  have all_three := disjointCheck_append first_two TerminalDisjoint.LastThird.checked
  simpa [terminalStates, leftLayers, rightLayers, leftOrdinaryC] using all_three

/-- No complete isolated-profile Cartesian choice for the distinguished fibre has zero syndrome. -/
theorem no_equal_cartesian_syndromes
    {leftPath rightPath : List Nat}
    (leftChoices : ChoicePath (isolatedLeftOptions 5) leftPath)
    (rightChoices : ChoicePath (isolatedRightOptions 5) rightPath) :
    leftPath.foldl (fun state increment => state ^^^ increment) 0 ≠
      rightPath.foldl (fun state increment => state ^^^ increment) 0 := by
  apply ne_of_disjointCheck terminal_disjoint
  · exact foldl_xor_mem_terminalStates left_chain (by simp) leftChoices
  · exact foldl_xor_mem_terminalStates right_chain (by simp) rightChoices

/-- Executable Cartesian-product membership is sufficient for the same syndrome exclusion. -/
theorem no_equal_of_mem_choices
    {leftPath rightPath : List Nat}
    (left_mem : leftPath ∈ choices (isolatedLeftOptions 5))
    (right_mem : rightPath ∈ choices (isolatedRightOptions 5)) :
    leftPath.foldl (fun state increment => state ^^^ increment) 0 ≠
      rightPath.foldl (fun state increment => state ^^^ increment) 0 :=
  no_equal_cartesian_syndromes
    (choicePath_of_mem_choices left_mem) (choicePath_of_mem_choices right_mem)

end PassantCodeQ13.WeightTen.IsolatedReachability.Fibre5
