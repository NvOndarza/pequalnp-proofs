import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace PEqualNPResearch.Incidence

-- Count incidences by their line fibres; the theorem is not a circuit bound.
theorem incidence_count (N k : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdegree : ∀ line : Fin N, Fintype.card {p : Fin N // I p line} = k) :
    Fintype.card {e : Fin N × Fin N // I e.1 e.2} = N * k := by
  let e : {e : Fin N × Fin N // I e.1 e.2} ≃
      (Σ line : Fin N, {p : Fin N // I p line}) :=
    { toFun := fun x => ⟨x.val.2, ⟨x.val.1, x.property⟩⟩
      invFun := fun x => ⟨(x.2.val, x.1), x.2.property⟩
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp [hdegree]

-- Two distinct points determine their common line uniquely.
theorem common_line_unique {N : ℕ} (I : Fin N → Fin N → Prop)
    (hplane : ∀ p r : Fin N, p ≠ r → ∃! line : Fin N, I p line ∧ I r line)
    {p r a b : Fin N} (hpr : p ≠ r)
    (hpa : I p a) (hra : I r a) (hpb : I p b) (hrb : I r b) : a = b := by
  obtain ⟨line, _, hunique⟩ := hplane p r hpr
  exact (hunique a ⟨hpa, hra⟩).trans (hunique b ⟨hpb, hrb⟩).symm

-- Hence two distinct lines cannot share two distinct points.
theorem no_incidence_rectangle {N : ℕ} (I : Fin N → Fin N → Prop)
    (hplane : ∀ p r : Fin N, p ≠ r → ∃! line : Fin N, I p line ∧ I r line)
    {p r a b : Fin N} (hpr : p ≠ r) (hab : a ≠ b) :
    ¬ (I p a ∧ I r a ∧ I p b ∧ I r b) := by
  rintro ⟨hpa, hra, hpb, hrb⟩
  exact hab (common_line_unique I hplane hpr hpa hra hpb hrb)

-- The common-point set of distinct lines has cardinality at most one.
theorem line_intersection_at_most_one {N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hplane : ∀ p r : Fin N, p ≠ r → ∃! line : Fin N, I p line ∧ I r line)
    {a b : Fin N} (hab : a ≠ b) :
    (Finset.univ.filter (fun p => I p a ∧ I p b)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  have hp' := (Finset.mem_filter.mp hp).2
  have hr' := (Finset.mem_filter.mp hr).2
  by_contra hpr
  exact no_incidence_rectangle I hplane hpr hab ⟨hp'.1, hr'.1, hp'.2, hr'.2⟩

-- Every all-incidence rectangle is a star: one side has at most one vertex.
-- This concerns rectangles in the incidence relation, not arbitrary circuit gates.
theorem rectangle_is_star {N : ℕ} (I : Fin N → Fin N → Prop)
    (hplane : ∀ p r : Fin N, p ≠ r → ∃! line : Fin N, I p line ∧ I r line)
    (A B : Finset (Fin N)) (hrect : ∀ p ∈ A, ∀ line ∈ B, I p line) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    have hlarge : 1 < A.card := by omega
    obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.mp hlarge
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact common_line_unique I hplane hpr
      (hrect p hp a ha) (hrect r hr a ha) (hrect p hp b hb) (hrect r hr b hb)

-- Counting a single all-incidence rectangle costs at least its edge count.
theorem rectangle_edge_count_le_cost {N : ℕ} (I : Fin N → Fin N → Prop)
    (hplane : ∀ p r : Fin N, p ≠ r → ∃! line : Fin N, I p line ∧ I r line)
    (A B : Finset (Fin N)) (hrect : ∀ p ∈ A, ∀ line ∈ B, I p line) :
    (A.product B).card ≤ A.card + B.card := by
  simp only [Finset.product_eq_sprod, Finset.card_product]
  rcases rectangle_is_star I hplane A B hrect with hA | hB
  · have h := Nat.mul_le_mul_right B.card hA
    simp only [one_mul] at h
    omega
  · have h := Nat.mul_le_mul_left A.card hB
    simp only [mul_one] at h
    omega

-- A cover by genuine incidence rectangles has total endpoint cost >= Nk.
-- The absent bridge is to extract such a cover cheaply from an arbitrary circuit.
theorem rectangle_cover_cost (N k m : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hdegree : ∀ line : Fin N, Fintype.card {p : Fin N // I p line} = k)
    (hplane : ∀ p r : Fin N, p ≠ r → ∃! line : Fin N, I p line ∧ I r line)
    (A B : Fin m → Finset (Fin N))
    (hrect : ∀ i, ∀ p ∈ A i, ∀ line ∈ B i, I p line)
    (hcover : ∀ p line, I p line → ∃ i, p ∈ A i ∧ line ∈ B i) :
    N * k ≤ ∑ i : Fin m, ((A i).card + (B i).card) := by
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  have hcard : E.card = N * k := by
    have hc : Fintype.card {e : Fin N × Fin N // I e.1 e.2} = E.card :=
      Fintype.card_of_finset' (p := {e : Fin N × Fin N | I e.1 e.2}) E
        (by intro e; simp [E])
    rw [← hc]
    exact incidence_count N k I hdegree
  have hs : E ⊆ Finset.univ.biUnion (fun i : Fin m => (A i).product (B i)) := by
    intro e he
    obtain ⟨i, hp, hl⟩ := hcover e.1 e.2 (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_product.mpr ⟨hp, hl⟩⟩
  calc
    N * k = E.card := hcard.symm
    _ ≤ (Finset.univ.biUnion (fun i : Fin m => (A i).product (B i))).card :=
      Finset.card_le_card hs
    _ ≤ ∑ i : Fin m, ((A i).product (B i)).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin m, ((A i).card + (B i).card) := by
      apply Finset.sum_le_sum
      intro i _
      exact rectangle_edge_count_le_cost I hplane (A i) (B i) (hrect i)

end PEqualNPResearch.Incidence
