import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace PEqualNPResearch.Matching

-- A finite family of pairwise vertex-disjoint edges needs one distinct
-- vertex in any set meeting every edge. No graph or circuit normal form
-- is assumed or established here.
theorem matching_cover_lower_bound {ι V : Type*} [Fintype ι] [DecidableEq V]
    (left right : ι → V)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hdisjoint : ∀ i j, left i ≠ right j)
    (T : Finset V) (hcover : ∀ i, left i ∈ T ∨ right i ∈ T) :
    Fintype.card ι ≤ T.card := by
  classical
  let f : ι → V := fun i => if left i ∈ T then left i else right i
  have hi : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    split_ifs at hab with ha hb
    · exact hleft hab
    · exact False.elim (hdisjoint a b hab)
    · exact False.elim (hdisjoint b a hab.symm)
    · exact hright hab
  have hm (i : ι) : f i ∈ T := by
    dsimp [f]
    split_ifs with h
    · exact h
    · exact (hcover i).resolve_left h
  have hs : Finset.univ.image f ⊆ T := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    exact hm i
  have hc : (Finset.univ.image f).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hi]
    simp
  have := Finset.card_le_card hs
  omega

-- Specialise to n independent pairs in the two consecutive natural blocks.
theorem diagonal_cover_lower_bound (n : ℕ) (T : Finset ℕ)
    (hcover : ∀ i : Fin n, i.val ∈ T ∨ n + i.val ∈ T) :
    n ≤ T.card := by
  have hl : Function.Injective (fun i : Fin n => i.val) := Fin.val_injective
  have hr : Function.Injective (fun i : Fin n => n + i.val) := by
    intro a b h
    change n + a.val = n + b.val at h
    apply Fin.ext
    omega
  have hd : ∀ i j : Fin n, i.val ≠ n + j.val := by
    intro i j
    have := i.isLt
    omega
  have h := matching_cover_lower_bound
    (fun i : Fin n => i.val) (fun i : Fin n => n + i.val) hl hr hd T hcover
  simpa using h

end PEqualNPResearch.Matching
