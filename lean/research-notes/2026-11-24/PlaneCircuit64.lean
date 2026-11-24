import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace PEqualNPResearch.PlaneCircuit64

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- This is a 64-gate upper bound, NOT the requested 63-gate witness.
def candidate : Circuit :=
  { gates := (List.range 13).flatMap (fun r =>
      [⟨GateOp.or, [r, (r + 1) % 13]⟩,
       ⟨GateOp.or, [26 + 4 * r, (r + 3) % 13]⟩,
       ⟨GateOp.or, [27 + 4 * r, (r + 9) % 13]⟩,
       ⟨GateOp.and, [28 + 4 * r, 13 + r]⟩]) ++
      (List.range 12).map (fun i =>
        ⟨GateOp.or, [if i = 0 then 29 else 77 + i, 33 + 4 * i]⟩),
    output := 89 }

def patterns : Fin 8 → ℕ × ℕ :=
  ![(7, 904), (13, 2848), (19, 708), (21, 2720),
    (25, 2656), (37, 2440), (41, 2370), (133, 808)]

def coefficients : Fin 3 → Fin 13 := ![1, 3, 9]

def boundary (pair : ℕ × ℕ) (a b : Fin 13) (swap : Bool) : Fin 26 → Bool :=
  let f : ℕ → ℕ → Fin 13 → Bool := fun m n v =>
    if swap = true then n.testBit (-(a * v + b)).val
    else m.testBit (a * v + b).val
  Fin.append (f pair.1 pair.2) (f pair.2 pair.1)

theorem candidate_monotone : Monotone2 candidate := by
  intro g hg
  simp only [candidate, List.mem_append, List.mem_flatMap, List.mem_map] at hg
  rcases hg with h | h
  · rcases h with ⟨r, _, h⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · rcases h with ⟨r, _, rfl⟩
    simp

theorem candidate_size : candidate.size = 64 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem one_positive : circuitFun 26 candidate (fun z =>
    decide (z = Fin.castAdd 13 (0 : Fin 13) ∨ z = Fin.natAdd 13 (0 : Fin 13))) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem positive_pairs : ∀ (b : Fin 13) (d : Fin 4),
    circuitFun 26 candidate (fun z =>
      decide (z = Fin.castAdd 13 (b + (![0, 1, 3, 9] : Fin 4 → Fin 13) d) ∨
        z = Fin.natAdd 13 b)) = true := by
  intro b d
  fin_cases b <;> fin_cases d <;> decide

end PEqualNPResearch.PlaneCircuit64
