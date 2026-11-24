import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

namespace PEqualNPResearch.Plane13

def line (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def admissible (x : Fin 13 → Bool) : Prop :=
  x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ line 0 → x v = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem line_card : ∀ t : Fin 13, (line t).card = 4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem distinct_intersection : ∀ t u : Fin 13, t ≠ u → (line t ∩ line u).card = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem complement_admissible : ∀ t : Fin 13,
    admissible (fun v => decide (v ∉ line t)) := by
  unfold admissible
  decide

end PEqualNPResearch.Plane13
