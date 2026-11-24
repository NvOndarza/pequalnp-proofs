import Mathlib.Order.Minimal
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNPResearch.Refute3316

def input (n : ℕ) : Fin 14 → Bool := fun i => n.testBit i.val

def badP : (Fin 14 → Bool) → Prop := fun x =>
  x = input 127 ∨ x = input 244 ∨ x = input 432

def claimed : Prop :=
  ∀ (P : (Fin 14 → Bool) → Prop),
    ∃ (C : Circuit) (op : GateOp) (i j : ℕ) (pair : ℕ × ℕ),
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 25 ∧ 14 ≤ i ∧ i < j ∧
        j < 14 + C.size ∧
        (op = GateOp.and ∧ pair ∈
          [(127, 244), (127, 432), (127, 3716), (127, 16256),
           (244, 314), (244, 432), (244, 792), (244, 1290), (244, 3716),
           (244, 7426), (432, 660), (432, 1220), (432, 1548)]) ∧
        (let wire : ℕ → (Fin 14 → Bool) → Bool := fun k x =>
          (C.wires (List.ofFn x)).getD k false
         let x := input pair.1
         let y := input pair.2
         let out : (Fin 14 → Bool) → Bool := fun z => op.eval [wire i z, wire j z]
         wire i x ≠ wire j x ∧ wire i x = wire j y ∧ wire j x = wire i y ∧
           (∀ z, Minimal P z →
             (op = GateOp.or ∧ (z = x ∨ z = y)) ∨ out z = true) ∧
           (∀ z, Maximal (fun w => ¬ P w) z →
             (op = GateOp.and ∧ (z = x ∨ z = y)) ∨ out z = false))

def bitOrder (x y : Fin 14 → Bool) : Prop := ∀ i, x i ≤ y i

theorem input_127_minimal : Minimal badP (input 127) := by
  rw [Minimal]
  constructor
  · exact Or.inl rfl
  · intro y hy hy_le
    rcases hy with h127 | h244 | h432
    · rw [h127]
    · have hbad : ¬ input 244 ≤ input 127 := by decide
      exact (hbad (h244 ▸ hy_le)).elim
    · have hbad : ¬ input 432 ≤ input 127 := by decide
      exact (hbad (h432 ▸ hy_le)).elim

theorem input_244_minimal : Minimal badP (input 244) := by
  rw [Minimal]
  constructor
  · exact Or.inr (Or.inl rfl)
  · intro y hy hy_le
    rcases hy with h127 | h244 | h432
    · have hbad : ¬ input 127 ≤ input 244 := by decide
      exact (hbad (h127 ▸ hy_le)).elim
    · rw [h244]
    · have hbad : ¬ input 432 ≤ input 244 := by decide
      exact (hbad (h432 ▸ hy_le)).elim

theorem input_432_minimal : Minimal badP (input 432) := by
  rw [Minimal]
  constructor
  · exact Or.inr (Or.inr rfl)
  · intro y hy hy_le
    rcases hy with h127 | h244 | h432
    · have hbad : ¬ input 127 ≤ input 432 := by decide
      exact (hbad (h127 ▸ hy_le)).elim
    · have hbad : ¬ input 244 ≤ input 432 := by decide
      exact (hbad (h244 ▸ hy_le)).elim
    · rw [h432]

theorem not_claimed : ¬ claimed := by
  intro h
  obtain ⟨C, op, i, j, pair, hmono, hsize, hi, hij, hj, hpair, hrest⟩ := h badP
  rcases hpair with ⟨hop, hmem⟩
  have hfirst : pair.1 = 127 ∨ pair.1 = 244 ∨ pair.1 = 432 := by
    simp at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp_all
  rcases hrest with ⟨hne, hcross1, hcross2, hmin, hmax⟩
  let x : Fin 14 → Bool := input pair.1
  let y : Fin 14 → Bool := input pair.2
  let wire : ℕ → (Fin 14 → Bool) → Bool := fun k z =>
    (C.wires (List.ofFn z)).getD k false
  let out : (Fin 14 → Bool) → Bool := fun z => op.eval [wire i z, wire j z]
  have hxP : badP x := by
    rcases hfirst with h | h | h <;> simp [x, badP, h]
  have hxminimal : Minimal badP x := by
    rcases hfirst with h | h | h
    · simpa [x, h] using input_127_minimal
    · simpa [x, h] using input_244_minimal
    · simpa [x, h] using input_432_minimal
  have hout : out x = false := by
    have hne' : wire i x ≠ wire j x := hne
    have hval : GateOp.and.eval [wire i x, wire j x] = false := by
      cases a : wire i x <;> cases b : wire j x <;>
        simp_all [GateOp.eval]
    simpa [out, hop] using hval
  have htrue : out x = true := by
    exact (hmin x hxminimal).resolve_left (by simp [hop])
  exact Bool.noConfusion (htrue.symm.trans hout)

end PEqualNPResearch.Refute3316


theorem PEqualNPResearch.Refute3316.not_posted_statement : ¬ (∀ (x1 : (Fin (14 : ℕ) → Bool) → Prop),   ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),     PEqualNP.MetaComplexity.Monotone2 x2 ∧       x2.size ≤ (25 : ℕ) ∧         (14 : ℕ) ≤ x4 ∧           x4 < x5 ∧             x5 < (14 : ℕ) + x2.size ∧               (x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6 ∈ [((127 : ℕ), (244 : ℕ)), ((127 : ℕ), (432 : ℕ)), ((127 : ℕ), (3716 : ℕ)), ((127 : ℕ), (16256 : ℕ)), ((244 : ℕ), (314 : ℕ)), ((244 : ℕ), (432 : ℕ)), ((244 : ℕ), (792 : ℕ)), ((244 : ℕ), (1290 : ℕ)), ((244 : ℕ), (3716 : ℕ)), ((244 : ℕ), (7426 : ℕ)), ((432 : ℕ), (660 : ℕ)), ((432 : ℕ), (1220 : ℕ)), ((432 : ℕ), (1548 : ℕ))]) ∧                 have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;                 have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;                 have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;                 have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];                 x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false) := by
  exact PEqualNPResearch.Refute3316.not_claimed
