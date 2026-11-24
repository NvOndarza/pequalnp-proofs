import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

namespace PEqualNPResearch.PetersenResidual

def petersenNine (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def petersenEight (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
  (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) ||
  (x 7 && x 4)

theorem petersen_false_vertex_four_restriction (x : Fin 8 → Bool) :
    petersenNine (Fin.insertNth (4 : Fin 9) false x) = petersenEight x := by
  fin_cases x <;> decide

end PEqualNPResearch.PetersenResidual

