import Erdos883FiniteCriterion
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos883Verified

/-- The number of three-odd-number blocks after removing the integer `1`. -/
theorem retainedOdds_eq_block_count (n : ℕ) :
    retainedOdds n = (n + 3) / 6 + 1 := by
  unfold retainedOdds
  omega

/-- Three consecutive odd integers are pairwise coprime: their nonzero
pairwise differences are `2` or `4`. -/
theorem coprime_of_odd_same_block {a b : ℕ} (ha : Odd a) (hb : Odd b)
    (hne : a ≠ b) (hblock : (a + 3) / 6 = (b + 3) / 6) : Nat.Coprime a b := by
  have htwo : Nat.Coprime a 2 := ha.coprime_two_right
  have hfour : Nat.Coprime a 4 := by
    simpa using htwo.mul_right htwo
  have htwo' : Nat.Coprime b 2 := hb.coprime_two_right
  have hfour' : Nat.Coprime b 4 := by
    simpa using htwo'.mul_right htwo'
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have hcases : b = a + 2 ∨ b = a + 4 ∨ a = b + 2 ∨ a = b + 4 := by omega
  rcases hcases with h | h | h | h
  · rw [h, Nat.coprime_self_add_right]
    exact htwo
  · rw [h, Nat.coprime_self_add_right]
    exact hfour
  · rw [h, Nat.coprime_self_add_left]
    exact htwo'.symm
  · rw [h, Nat.coprime_self_add_left]
    exact hfour'.symm

/-- For the odd-integer specialization needed here, the AK endpoint input
has an elementary direct proof. If `1` is absent, map each odd number to its
block `{6k+3, 6k+5, 6k+7}` and use the finite pigeonhole principle. -/
theorem oddEndpointPrinciple : OddEndpointPrinciple := by
  intro n hn Y hY hcard
  classical
  have htwo : 2 ≤ Y.card := by
    rw [retainedOdds_eq_block_count] at hcard
    omega
  by_cases hOne : 1 ∈ Y
  · obtain ⟨b, hb, hne⟩ := Finset.exists_mem_ne htwo 1
    exact ⟨1, hOne, b, hb, hne.symm, Nat.coprime_one_left b⟩
  · have hmaps : Set.MapsTo (fun a : ℕ => (a + 3) / 6) Y
        (Finset.Icc 1 ((n + 3) / 6)) := by
      intro a ha
      obtain ⟨hai, hao⟩ := Finset.mem_filter.mp (hY ha)
      obtain ⟨hpos, hbound⟩ := Finset.mem_Icc.mp hai
      obtain ⟨x, hx⟩ := hao
      have hne : a ≠ 1 := fun h => hOne (h ▸ ha)
      apply Finset.mem_Icc.mpr
      dsimp
      constructor <;> omega
    have hsize : (Finset.Icc 1 ((n + 3) / 6)).card < Y.card := by
      rw [Nat.card_Icc]
      rw [retainedOdds_eq_block_count] at hcard
      omega
    obtain ⟨a, ha, b, hb, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hsize hmaps
    exact ⟨a, ha, b, hb, hne,
      coprime_of_odd_same_block (Finset.mem_filter.mp (hY ha)).2
        (Finset.mem_filter.mp (hY hb)).2 hne heq⟩

/-- The endpoint hypothesis of the finite interval criterion is now discharged. -/
theorem exact_interval_criterion_with_proved_endpoints
    {L U : ℕ} (hL : 6 ≤ L)
    (O ps : List ℕ) (hO : O.Nodup) (hOset : O.toFinset = oddUniverse U)
    (hcert : ExactIntervalCertificate L U O ps)
    {n : ℕ} (hLn : L ≤ n) (hnU : n ≤ U)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths :=
  exact_interval_criterion_sound oddEndpointPrinciple hL O ps hO hOset hcert
    hLn hnU A hA hdense hk hkn

/-- Only the covering family of arithmetic interval certificates remains an input. -/
theorem firstQuestion_of_interval_cover_with_proved_endpoints
    (hcover : ∀ n : ℕ, 6 ≤ n →
      ∃ L U : ℕ, ∃ O ps : List ℕ,
        6 ≤ L ∧ L ≤ n ∧ n ≤ U ∧ O.Nodup ∧
        O.toFinset = oddUniverse U ∧ ExactIntervalCertificate L U O ps) :
    Erdos883Target.FirstQuestion :=
  firstQuestion_of_interval_cover oddEndpointPrinciple hcover

#print axioms retainedOdds_eq_block_count
#print axioms coprime_of_odd_same_block
#print axioms oddEndpointPrinciple
#print axioms exact_interval_criterion_with_proved_endpoints
#print axioms firstQuestion_of_interval_cover_with_proved_endpoints

end Erdos883Verified
