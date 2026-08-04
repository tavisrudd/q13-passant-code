import PassantCodeQ13.AssociationAlgebra
import PassantCodeQ13.MinimumWords.Reconstruction
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Binary matrix semantics for association and orbit certificates

This module evaluates relation and orbit matrices over `Bool`, then proves once that Boolean parity
linearizes to ordinary matrix multiplication over `ZMod 2`.  Finite leaves never perform field
arithmetic; their aggregators transport only compact entry checks through
`booleanParityProduct_linearize`.
-/

namespace PassantCodeQ13.AssociationTransport

open PassantCodeQ13.AssociationAlgebra
open RelativeConicArcs.PassantCodeQ13

/-- The 78 indexed internal points used as code coordinates. -/
abbrev Coordinate := Fin 78

/-- The 91 rows in each displayed projective minimum-word orbit. -/
abbrev OrbitCoordinate := Fin 91

/-- Embed a Boolean parity value in the binary field. -/
def boolValue (value : Bool) : ZMod 2 :=
  if value then 1 else 0

/-- Entrywise linearization of a Boolean matrix over the binary field. -/
def booleanMatrix {Rows Columns : Type*} (matrix : Matrix Rows Columns Bool) :
    Matrix Rows Columns (ZMod 2) :=
  fun row column => boolValue (matrix row column)

/-- Boolean zero matrix. -/
def booleanZeroMatrix {Rows Columns : Type*} : Matrix Rows Columns Bool :=
  fun _ _ => false

/-- Boolean identity matrix. -/
def booleanIdentityMatrix {card : Nat} : Matrix (Fin card) (Fin card) Bool :=
  fun row column => decide (row = column)

/-- Entrywise Boolean exclusive-or. -/
def booleanXorMatrix {Rows Columns : Type*}
    (left right : Matrix Rows Columns Bool) : Matrix Rows Columns Bool :=
  fun row column => xor (left row column) (right row column)

/-- Linearization sends the Boolean zero matrix to zero. -/
theorem booleanMatrix_zero {Rows Columns : Type*} :
    booleanMatrix (booleanZeroMatrix : Matrix Rows Columns Bool) = 0 := by
  rfl

/-- Linearization commutes with matrix transpose. -/
theorem booleanMatrix_transpose {Rows Columns : Type*} (matrix : Matrix Rows Columns Bool) :
    booleanMatrix matrix.transpose = (booleanMatrix matrix).transpose := by
  rfl

/-- Linearization sends the Boolean identity matrix to the binary identity. -/
theorem booleanMatrix_identity {card : Nat} :
    booleanMatrix (booleanIdentityMatrix : Matrix (Fin card) (Fin card) Bool) = 1 := by
  ext row column
  by_cases equal : row = column <;>
    simp [booleanMatrix, booleanIdentityMatrix, boolValue, Matrix.one_apply, equal]

/-- Linearization sends entrywise exclusive-or to binary matrix addition. -/
theorem booleanMatrix_xor {Rows Columns : Type*}
  (left right : Matrix Rows Columns Bool) :
    booleanMatrix (booleanXorMatrix left right) = booleanMatrix left + booleanMatrix right := by
  ext row column
  have one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
  cases leftValue : left row column <;> cases rightValue : right row column <;>
    simp [booleanMatrix, booleanXorMatrix, boolValue, leftValue, rightValue, one_add_one]

/-- Boolean adjacency matrix of one elliptic relation. -/
def relationBooleanMatrix (value : Field13) : Matrix Coordinate Coordinate Bool :=
  fun row column => row != column && rhoAt row.1 column.1 == value

/-- The binary adjacency matrix of one elliptic relation. -/
def relationLinearMatrix (value : Field13) : Matrix Coordinate Coordinate (ZMod 2) :=
  booleanMatrix (relationBooleanMatrix value)

/-- Boolean support matrix of one displayed projective orbit. -/
def orbitSupportBooleanMatrix (orbit : List Nat) : Matrix OrbitCoordinate Coordinate Bool :=
  fun row column => (orbit.getD row.1 0).testBit column.1

/-- The 91-by-78 support matrix of one displayed projective orbit. -/
def orbitSupportMatrix (orbit : List Nat) : Matrix OrbitCoordinate Coordinate (ZMod 2) :=
  booleanMatrix (orbitSupportBooleanMatrix orbit)

/-- Boolean parity product, before linearization over the binary field. -/
def booleanParityProduct {Rows Columns : Type*} {middleCard : Nat}
    (left : Matrix Rows (Fin middleCard) Bool)
    (right : Matrix (Fin middleCard) Columns Bool) : Matrix Rows Columns Bool :=
  fun row column =>
    ((List.ofFn fun middle : Fin middleCard => left row middle && right middle column).foldl
      (fun parity term => if term then !parity else parity) false)

/-- Compact Boolean equality check for finite Boolean matrices. -/
def booleanMatrixEqualityCheck {rowCard columnCard : Nat}
    (left right : Matrix (Fin rowCard) (Fin columnCard) Bool) : Bool :=
  (List.ofFn fun row : Fin rowCard =>
    (List.ofFn fun column : Fin columnCard => left row column == right row column).all id
  ).all id

/-- A successful compact Boolean entry check gives extensional matrix equality. -/
theorem booleanMatrixEqualityCheck_sound {rowCard columnCard : Nat}
    {left right : Matrix (Fin rowCard) (Fin columnCard) Bool}
    (checked : booleanMatrixEqualityCheck left right = true) : left = right := by
  ext row column
  simp only [booleanMatrixEqualityCheck, List.all_eq_true, List.forall_mem_ofFn_iff, id_eq] at checked
  exact eq_of_beq (checked row column)

private theorem parityFold_value
    (conditions : List Bool) (initial : Bool) :
    boolValue (conditions.foldl (fun parity term => if term then !parity else parity) initial) =
      boolValue initial + (conditions.map boolValue).sum := by
  induction conditions generalizing initial with
  | nil => simp [boolValue]
  | cons condition conditions inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      have one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
      cases initial <;> cases condition <;> simp [boolValue]
      rw [← add_assoc, one_add_one, zero_add]

/-- Boolean parity multiplication linearizes to matrix multiplication over `ZMod 2`. -/
theorem booleanParityProduct_linearize {Rows Columns : Type*} {middleCard : Nat}
    (left : Matrix Rows (Fin middleCard) Bool)
    (right : Matrix (Fin middleCard) Columns Bool) :
    booleanMatrix (booleanParityProduct left right) =
      booleanMatrix left * booleanMatrix right := by
  ext row column
  rw [Matrix.mul_apply]
  change boolValue
      ((List.ofFn fun middle : Fin middleCard => left row middle && right middle column).foldl
        (fun parity term => if term then !parity else parity) false) = _
  rw [parityFold_value]
  simp only [boolValue, Bool.false_eq_true, ↓reduceIte, zero_add, List.map_ofFn,
    Function.comp_apply, List.sum_ofFn, booleanMatrix]
  apply Finset.sum_congr rfl
  intro middle _
  cases left row middle <;> cases right middle column <;> rfl

end PassantCodeQ13.AssociationTransport
