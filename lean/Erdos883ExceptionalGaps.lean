import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.SuccPred

namespace Erdos883Verified

/-- A path gap touches a bad skeleton vertex at one of its two endpoints. -/
def touchedGaps {k : ℕ} (B : Finset (Fin (k + 1))) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.castSucc ∈ B ∨ i.succ ∈ B)

/-- Every bad skeleton vertex is incident to at most two linear gaps. -/
theorem touchedGaps_card_le {k : ℕ} (B : Finset (Fin (k + 1))) :
    (touchedGaps B).card ≤ 2 * B.card := by
  let L : Finset (Fin k) := Finset.univ.filter (fun i => i.castSucc ∈ B)
  let R : Finset (Fin k) := Finset.univ.filter (fun i => i.succ ∈ B)
  have hL : L.card ≤ B.card := by
    rw [← Finset.card_image_of_injective L (Fin.castSucc_injective k)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  have hR : R.card ≤ B.card := by
    rw [← Finset.card_image_of_injective R (Fin.succ_injective k)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  have heq : touchedGaps B = L ∪ R := by
    ext i
    simp [touchedGaps, L, R]
  rw [heq]
  have hu := Finset.card_union_le L R
  omega

/-- Combining low-profile incidence and signature-transition exceptions gives
exactly the manuscript's rankwise budget. -/
theorem exceptional_gap_budget {k R b h j : ℕ}
    (B : Finset (Fin (k + 1))) (cross : Finset (Fin k))
    (hB : B.card ≤ R - b) (hcross : cross.card ≤ h)
    (hbudget : 2 * (R - b) + h < j) :
    (touchedGaps B ∪ cross).card < j := by
  have htouch := touchedGaps_card_le B
  have hsum := Finset.card_union_le (touchedGaps B) cross
  omega

#print axioms touchedGaps_card_le
#print axioms exceptional_gap_budget
end Erdos883Verified
