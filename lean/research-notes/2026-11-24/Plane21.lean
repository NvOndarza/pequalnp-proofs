import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace PEqualNPResearch.Plane21

def edges : List (ℕ × ℕ) := [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma diagonal : ∀ u : Fin 21, (u.val, 21 + u.val) ∈ edges := by
  decide

lemma cover_lower_bound (T : Finset ℕ)
    (h : ∀ u v, (u, v) ∈ edges → u ∈ T ∨ v ∈ T) : 21 ≤ T.card := by
  classical
  let f : Fin 21 → ℕ := fun u => if u.val ∈ T then u.val else 21 + u.val
  have hi : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    dsimp [f] at hab
    split_ifs at hab <;> omega
  have hm (u : Fin 21) : f u ∈ T := by
    dsimp [f]
    split_ifs with hu
    · exact hu
    · exact (h _ _ (diagonal u)).resolve_left hu
  have hs : Finset.univ.image f ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨u, _, rfl⟩
    exact hm u
  have hc : (Finset.univ.image f).card = 21 := by
    rw [Finset.card_image_of_injective _ hi]
    simp
  have := Finset.card_le_card hs
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma edge_count : edges.length = 105 := by decide

lemma cover_cost (T : Finset ℕ)
    (h : ∀ u v, (u, v) ∈ edges → u ∈ T ∨ v ∈ T) :
    125 ≤ edges.length + T.card - 1 := by
  have hc := cover_lower_bound T h
  rw [edge_count]
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 20000 in
lemma pair_unique : ∀ a b : Fin 21, a ≠ b →
    ∃! v : Fin 21, (a.val, 21 + v.val) ∈ edges ∧ (b.val, 21 + v.val) ∈ edges := by
  simp only [ExistsUnique]
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma left_endpoints : ∀ e ∈ edges, e.1 < 21 := by decide

lemma left_cover_exact : ∃ T : Finset ℕ, T.card = 21 ∧
    ∀ u v, (u, v) ∈ edges → u ∈ T ∨ v ∈ T := by
  refine ⟨Finset.range 21, by simp, ?_⟩
  intro u v h
  exact Or.inl (Finset.mem_range.mpr (left_endpoints (u, v) h))

end PEqualNPResearch.Plane21
