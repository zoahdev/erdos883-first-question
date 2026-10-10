import Erdos883SecondNearBase

/-! The finite near-U construction from explicit rational/integer inequalities.
This file does not assert that the certificate holds eventually for all near-U
sets, and does not assert the full second question. Its hypotheses expose the
remaining quantitative selection of parameters. -/

namespace Erdos883Second.Near

open Erdos883Verified

/-- Purely numerical sufficient conditions. The support condition is an integer
power comparison; the other conditions include every finite rounding error. -/
structure FiniteCertificate (n : ℕ) (A : Finset ℕ) (l k r E : ℕ) (z : ℚ) : Prop where
  n_pos : 1 ≤ n
  z_pos : 0 < z
  good_apex : momentConstant k * n * z ^ k < ((A \ standardUniverse n).card : ℚ)
  support_error : supportConstant r ^ r * n ^ (l + 1) < (E + 1) ^ r
  left_budget : ((standardUniverse n \ A).card : ℚ) +
    momentConstant k * n * z ^ k + l ≤ (n : ℚ) / 6 * z - 2 * E - 1
  right_budget : ((standardUniverse n \ A).card : ℚ) + l ≤
    (n : ℚ) / 2 * z ^ (l + 1) - E - 1

private theorem odd_finset_prod (B : Finset ℕ) (hB : ∀ b ∈ B, Odd b) :
    Odd (∏ b ∈ B, b) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.prod_insert hb]
    exact (hB b (Finset.mem_insert_self _ _)).mul
      (ih (fun x hx => hB x (Finset.mem_insert_of_mem hx)))

/-- A checked finite certificate constructs the actual three disjoint vertex
parts and all cross-part coprime edges. No graph-theoretic result is assumed. -/
theorem finite_tripartite_of_certificate {n l k r E : ℕ} {A : Finset ℕ} {z : ℚ}
    (hA : A ⊆ Finset.Icc 1 n) (H : FiniteCertificate n A l k r E z) :
    ContainsTripartite A l := by
  classical
  let T := A \ standardUniverse n
  let M := standardUniverse n \ A
  have hT : T ⊆ Finset.Icc 1 n := by
    intro a ha; exact hA (Finset.mem_sdiff.mp ha).1
  obtain ⟨a, haT, haz⟩ := good_totient_in_subset hT H.z_pos H.good_apex
  have haA : a ∈ A := (Finset.mem_sdiff.mp haT).1
  have haU : a ∉ standardUniverse n := (Finset.mem_sdiff.mp haT).2
  have haI := Finset.mem_Icc.mp (hA haA)
  have ha : 0 < a := haI.1
  have han : a ≤ n := haI.2
  have ha6 : Nat.Coprime a 6 := extra_mem_coprime_six hA haT
  have haodd : Odd a := Nat.coprime_two_right.mp
    (ha6.of_dvd_right (by decide : 2 ∣ 6))
  have hna : a ≤ n ^ (l + 1) := by
    calc
      a ≤ n := han
      _ = n * 1 := by simp
      _ ≤ n * n ^ l := Nat.mul_le_mul_left n (one_le_pow₀ H.n_pos)
      _ = _ := by rw [pow_succ]; ring
  have hae : 2 ^ a.primeFactors.card ≤ E :=
    support_error_le_of_certificate ha hna H.support_error
  have haeQ : ((2 ^ a.primeFactors.card : ℕ) : ℚ) ≤ E := by exact_mod_cast hae
  let S := leftCandidates n a
  have hS : S ⊆ standardUniverse n := by
    intro b hb
    have hm := leftCandidates_mem ha6 hb
    exact Finset.mem_filter.mpr ⟨hm.1, Or.inr hm.2.2.1⟩
  let G := goodSelected A S z
  have hdel : (S.card : ℚ) ≤ (G.card : ℚ) + M.card +
      (((Finset.Icc 1 n).filter (fun v => totientDensity v < z)).card : ℚ) := by
    exact_mod_cast candidate_card_le_good_missing_bad (A := A) (z := z) hS
  have hbad := totient_below_card_le n k H.z_pos
  have hleft0 := leftCandidates_card_ge (n := n) ha haodd
  have hscale := mul_le_mul_of_nonneg_left haz
    (by positivity : (0 : ℚ) ≤ (n : ℚ) / 6)
  have hleft : (n : ℚ) / 6 * z - 2 * E - 1 ≤ (S.card : ℚ) := by
    dsimp [S]
    push_cast at hleft0 haeQ
    linarith
  have hGcard : l ≤ G.card := by
    have hh : (l : ℚ) ≤ G.card := by
      have hbudget := H.left_budget
      change (M.card : ℚ) + momentConstant k * n * z ^ k + l ≤ _ at hbudget
      linarith
    exact_mod_cast hh
  obtain ⟨B, hBG, hBcard⟩ := Finset.exists_subset_card_eq hGcard
  have hBmem (b : ℕ) (hb : b ∈ B) :
      b ∈ Finset.Icc 1 n ∧ Odd b ∧ 3 ∣ b ∧ Nat.Coprime a b := by
    exact leftCandidates_mem ha6 (Finset.mem_inter.mp (Finset.mem_filter.mp (hBG hb)).1).1
  have hBA : B ⊆ A := by
    intro b hb
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp (hBG hb)).1).2
  have hBz : ∀ b ∈ B, z ≤ totientDensity b := by
    intro b hb; exact (Finset.mem_filter.mp (hBG hb)).2
  have hBpos : ∀ b ∈ B, 0 < b := by
    intro b hb; exact (Finset.mem_Icc.mp (hBmem b hb).1).1
  have hBn : ∀ b ∈ B, b ≤ n := by
    intro b hb; exact (Finset.mem_Icc.mp (hBmem b hb).1).2
  have hBodd : ∀ b ∈ B, Odd b := fun b hb => (hBmem b hb).2.1
  let q := a * ∏ b ∈ B, b
  have hq : 0 < q := Nat.mul_pos ha (Finset.prod_pos hBpos)
  have hqn : q ≤ n ^ (l + 1) := by
    simpa only [hBcard] using product_le_pow han hBn
  have hqe : 2 ^ q.primeFactors.card ≤ E :=
    support_error_le_of_certificate hq hqn H.support_error
  have hqeQ : ((2 ^ q.primeFactors.card : ℕ) : ℚ) ≤ E := by exact_mod_cast hqe
  have hqz : z ^ (l + 1) ≤ totientDensity q := by
    simpa only [hBcard] using product_density_ge_pow ha hBpos H.z_pos.le haz hBz
  have hqodd : Odd q := haodd.mul (odd_finset_prod B hBodd)
  let R := rightCandidates n q
  have hR : R ⊆ standardUniverse n := by
    intro c hc
    have hm := rightCandidates_mem hqodd hc
    exact Finset.mem_filter.mpr ⟨hm.1, Or.inl hm.2.1.two_dvd⟩
  have hright0 := rightCandidates_card_ge (n := n) hq
  have hqscale := mul_le_mul_of_nonneg_left hqz
    (by positivity : (0 : ℚ) ≤ (n : ℚ) / 2)
  have hright : (n : ℚ) / 2 * z ^ (l + 1) - E - 1 ≤ (R.card : ℚ) := by
    dsimp [R]
    linarith
  have hmissing : (R \ A).card ≤ M.card := by
    apply Finset.card_le_card
    intro c hc
    obtain ⟨hcR, hcA⟩ := Finset.mem_sdiff.mp hc
    exact Finset.mem_sdiff.mpr ⟨hR hcR, hcA⟩
  have hsplit := Finset.card_sdiff_add_card_inter R A
  have hRC : l ≤ (R ∩ A).card := by
    have hmQ : ((R \ A).card : ℚ) ≤ M.card := by exact_mod_cast hmissing
    have hsQ : ((R \ A).card : ℚ) + (R ∩ A).card = R.card := by exact_mod_cast hsplit
    have hbudget := H.right_budget
    change (M.card : ℚ) + l ≤ _ at hbudget
    have hh : (l : ℚ) ≤ (R ∩ A).card := by linarith
    exact_mod_cast hh
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hRC
  have hCmem (c : ℕ) (hc : c ∈ C) :
      c ∈ Finset.Icc 1 n ∧ Even c ∧ Nat.Coprime c q :=
    rightCandidates_mem hqodd (Finset.mem_inter.mp (hCsub hc)).1
  have hCA : C ⊆ A := fun c hc => (Finset.mem_inter.mp (hCsub hc)).2
  have hadvd : a ∣ q := dvd_mul_right a _
  have hbdvd (b : ℕ) (hb : b ∈ B) : b ∣ q :=
    (Finset.dvd_prod_of_mem (fun b : ℕ => b) hb).trans (dvd_mul_left _ a)
  let W : FinsetWitness A l := {
    apex := a
    left := B
    right := C
    apex_mem := haA
    left_subset := hBA
    right_subset := hCA
    left_card := hBcard
    right_card := hCcard
    apex_not_left := by
      intro haB
      exact haU (Finset.mem_filter.mpr ⟨hA haA, Or.inr (hBmem a haB).2.2.1⟩)
    apex_not_right := by
      intro haC
      exact (Nat.not_even_iff_odd.mpr haodd) (hCmem a haC).2.1
    disjoint := by
      apply Finset.disjoint_left.mpr
      intro v hvB hvC
      exact (Nat.not_even_iff_odd.mpr (hBodd v hvB)) (hCmem v hvC).2.1
    apex_left_coprime := fun b hb => (hBmem b hb).2.2.2
    apex_right_coprime := fun c hc => ((hCmem c hc).2.2.of_dvd_right hadvd).symm
    left_right_coprime := fun b hb c hc =>
      ((hCmem c hc).2.2.of_dvd_right (hbdvd b hb)).symm }
  exact W.contains

#print axioms finite_tripartite_of_certificate

end Erdos883Second.Near


