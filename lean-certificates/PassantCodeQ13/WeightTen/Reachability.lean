import PassantCodeQ13.WeightTen.Base
import Mathlib.Data.Nat.Bitwise

/-!
# Kernel-checked Cartesian syndrome reachability

A finite syndrome certificate may replace one large Cartesian elaboration by a sequence of explicit
reachable-state lists.  At each stage, the checker verifies exact equality with the Cartesian
traversal obtained by XORing every current state with every allowed increment.  The soundness
theorem then proves, independently of how the lists were generated, that the last list contains the
XOR of every complete Cartesian choice.

Exact traversal equality also checks multiplicity and order, although the soundness theorem needs
only coverage.  External generation therefore carries no logical authority.  The mathematical
conclusion follows from the kernel-checked transition tables and the theorem below.
-/

namespace PassantCodeQ13.WeightTen.Reachability

/-- Pack the indicated syndrome-row bits, in list order, into a compact natural number. -/
def selectBits : List Nat → Nat → Nat
  | [], _ => 0
  | row :: rows, syndrome =>
      Nat.bit (syndrome.testBit row) (selectBits rows syndrome)

/-- Selecting syndrome bits commutes with binary syndrome addition. -/
theorem selectBits_xor (rows : List Nat) (first second : Nat) :
    selectBits rows (first ^^^ second) = selectBits rows first ^^^ selectBits rows second := by
  induction rows with
  | nil => simp [selectBits]
  | cons row rows induction =>
      simp only [selectBits, Nat.testBit_xor, induction]
      rw [Nat.xor_bit]

/-- Selecting bits after an XOR fold equals folding the selected increments. -/
theorem selectBits_foldl_xor (rows path : List Nat) (start : Nat) :
    selectBits rows (path.foldl (fun state increment => state ^^^ increment) start) =
      (path.map (selectBits rows)).foldl (fun state increment => state ^^^ increment)
        (selectBits rows start) := by
  induction path generalizing start with
  | nil => rfl
  | cons increment tail induction =>
      simp only [List.foldl_cons, List.map_cons]
      rw [induction, selectBits_xor]

/-- A list selects one allowed syndrome increment at each Cartesian stage. -/
inductive ChoicePath : List (List Nat) → List Nat → Prop
  | nil : ChoicePath [] []
  | cons {options remaining choice tail} :
      choice ∈ options → ChoicePath remaining tail →
        ChoicePath (options :: remaining) (choice :: tail)

/-- Membership in the executable Cartesian product supplies one choice at every stage. -/
theorem choicePath_of_mem_choices {options : List (List Nat)} {path : List Nat}
    (path_mem : path ∈ PassantCodeQ13.WeightTen.choices options) :
    ChoicePath options path := by
  induction options generalizing path with
  | nil =>
      simp only [PassantCodeQ13.WeightTen.choices, List.mem_singleton] at path_mem
      subst path
      exact .nil
  | cons available remaining induction =>
      simp only [PassantCodeQ13.WeightTen.choices, List.mem_flatMap, List.mem_map] at path_mem
      obtain ⟨choice, choice_mem, tail, tail_mem, path_eq⟩ := path_mem
      subst path
      exact .cons choice_mem (induction tail_mem)

/-- Applying a function to every option and choice preserves Cartesian coverage. -/
theorem ChoicePath.map {options : List (List Nat)} {path : List Nat}
    (path_choices : ChoicePath options path) (transform : Nat → Nat) :
    ChoicePath (options.map (List.map transform)) (path.map transform) := by
  induction path_choices with
  | nil => exact .nil
  | cons choice_mem _ induction =>
      exact .cons (List.mem_map.mpr ⟨_, choice_mem, rfl⟩) induction

/-- The one-step XOR successors in Cartesian traversal order. -/
def transitionSuccessors (current options : List Nat) : List Nat :=
  current.flatMap fun state => options.map fun increment => state ^^^ increment

/-- Check that `next` is the one-step XOR successor list in Cartesian traversal order. -/
def transitionCheck (current options next : List Nat) : Bool :=
  transitionSuccessors current options == next

/-- Check a sequence of post-transition state lists against a Cartesian list of increments. -/
def chainCheck : List Nat → List (List Nat) → List (List Nat) → Bool
  | _, [], [] => true
  | current, options :: remaining, next :: later =>
      transitionCheck current options next && chainCheck next remaining later
  | _, _, _ => false

/-- A checked first transition and a checked tail assemble into a checked transition chain. -/
theorem chainCheck_cons_of_transitionCheck
    {current options next : List Nat} {remaining later : List (List Nat)}
    (first_checked : transitionCheck current options next = true)
    (later_checked : chainCheck next remaining later = true) :
    chainCheck current (options :: remaining) (next :: later) = true := by
  simp [chainCheck, first_checked, later_checked]

/-- The empty Cartesian transition sequence is checked. -/
theorem chainCheck_nil (current : List Nat) : chainCheck current [] [] = true := by
  rfl

/-- The terminal state list of a certificate, or the initial list when there are no transitions. -/
def terminalStates (initial : List Nat) : List (List Nat) → List Nat
  | [] => initial
  | first :: later => terminalStates first later

/-- Check that two explicit state lists are disjoint. -/
def disjointCheck (first second : List Nat) : Bool :=
  first.all fun state => !second.contains state

/-- Disjointness checks on two left-hand pieces combine across concatenation. -/
theorem disjointCheck_append {first second third : List Nat}
    (first_checked : disjointCheck first third = true)
    (second_checked : disjointCheck second third = true) :
    disjointCheck (first ++ second) third = true := by
  unfold disjointCheck at first_checked second_checked ⊢
  rw [List.all_append, first_checked, second_checked]
  rfl

/-- A successful disjointness check excludes equality between arbitrary members of the lists. -/
theorem ne_of_disjointCheck {first second : List Nat}
    (checked : disjointCheck first second = true)
    {left right : Nat} (left_mem : left ∈ first) (right_mem : right ∈ second) :
    left ≠ right := by
  intro equal
  have absent_bool := (List.all_eq_true.mp checked) left left_mem
  have absent : second.contains left = false := by
    simpa using absent_bool
  have present : second.contains left = true :=
    List.contains_iff_mem.mpr (equal ▸ right_mem)
  rw [present] at absent
  exact Bool.noConfusion absent

/-- A successful transition check contains each indicated one-step successor. -/
theorem mem_next_of_transitionCheck
    {current options next : List Nat} (checked : transitionCheck current options next = true)
    {state increment : Nat} (state_mem : state ∈ current) (increment_mem : increment ∈ options) :
    state ^^^ increment ∈ next := by
  have next_eq : transitionSuccessors current options = next := by
    simpa [transitionCheck] using checked
  rw [← next_eq]
  simp only [transitionSuccessors, List.mem_flatMap, List.mem_map]
  exact ⟨state, state_mem, increment, increment_mem, rfl⟩

/-- Every complete Cartesian choice reaches the terminal list of a successful chain certificate. -/
theorem foldl_xor_mem_terminalStates
    {initial : List Nat} {options layers : List (List Nat)}
    (checked : chainCheck initial options layers = true)
    {start : Nat} (start_mem : start ∈ initial)
    {path : List Nat} (path_choices : ChoicePath options path) :
    path.foldl (fun state increment => state ^^^ increment) start ∈
      terminalStates initial layers := by
  induction path_choices generalizing initial layers start with
  | nil =>
      cases layers with
      | nil => simpa [terminalStates]
      | cons first later => simp [chainCheck] at checked
  | @cons options remaining choice tail choice_mem tail_choices induction =>
      cases layers with
      | nil => simp [chainCheck] at checked
      | cons next later =>
          have checks : transitionCheck initial options next = true ∧
              chainCheck next remaining later = true := by
            simpa [chainCheck] using checked
          have transition_checked : transitionCheck initial options next = true := by
            exact checks.1
          have later_checked : chainCheck next remaining later = true := by
            exact checks.2
          have successor_mem : start ^^^ choice ∈ next :=
            mem_next_of_transitionCheck transition_checked start_mem choice_mem
          simpa [terminalStates] using
            induction later_checked successor_mem

/-- If the terminal list omits a target, no covered Cartesian choice has that XOR value. -/
theorem foldl_xor_ne_of_not_mem_terminalStates
    {initial : List Nat} {options layers : List (List Nat)}
    (checked : chainCheck initial options layers = true)
    {start : Nat} (start_mem : start ∈ initial)
    {path : List Nat} (path_choices : ChoicePath options path)
    {target : Nat} (target_absent : target ∉ terminalStates initial layers) :
    path.foldl (fun state increment => state ^^^ increment) start ≠ target := by
  intro equal
  apply target_absent
  rw [← equal]
  exact foldl_xor_mem_terminalStates checked start_mem path_choices

/-- A compact selected-bit certificate excludes an equality in the full 78-bit syndrome space.
The hypothesis `ChoicePath options path` is the complete Cartesian-domain bridge: it records one
choice from every supplied option list, with no sampling or generated coverage assumption. -/
theorem full_xor_ne_of_selectedBits_certificate
    (rows : List Nat) {initial : List Nat} {options layers : List (List Nat)}
    (checked : chainCheck initial (options.map (List.map (selectBits rows))) layers = true)
    {start : Nat} (start_mem : selectBits rows start ∈ initial)
    {path : List Nat} (path_choices : ChoicePath options path)
    {target : Nat} (target_absent : selectBits rows target ∉ terminalStates initial layers) :
    path.foldl (fun state increment => state ^^^ increment) start ≠ target := by
  intro equal
  have projected_path := path_choices.map (selectBits rows)
  have reached := foldl_xor_mem_terminalStates checked start_mem projected_path
  apply target_absent
  rw [← equal, selectBits_foldl_xor]
  exact reached

end PassantCodeQ13.WeightTen.Reachability
