import Erdos883ProfileCriterion
import Erdos883EulerBound
import Erdos883ImprovedRanks
import Erdos883ImprovedAccounting
import Erdos883ImprovedNeighbors
import Erdos883RefinedCdfBounds
import Erdos883RealResources

namespace Erdos883Verified.Improved

set_option maxHeartbeats 1000000

noncomputable abbrev realTotientLowCount (n : ℕ) (t : ℝ) : ℕ :=
  lowProfileCount (fun v => (totientDensity v : ℝ)) n t

/-- The normalization identity keeps the integer low-profile count exact. -/
theorem realTotientLowCount_normalization {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (realTotientLowCount n t : ℝ) / (n / 6 : ℕ) =
      ((n : ℝ) / (2 * (n / 6 : ℕ))) *
        ((2 / (n : ℝ)) * (realTotientLowCount n t : ℝ)) := by
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- A finite CDF at most one has a uniform normalized integer-count error. -/
theorem large_count_of_cdf_le_one {n : ℕ} {t : ℝ} (hn : 200000 ≤ n)
    (hG : (2 / (n : ℝ)) * (realTotientLowCount n t : ℝ) ≤ 1) :
    (realTotientLowCount n t : ℝ) / (n / 6 : ℕ) <
      3 * ((2 / (n : ℝ)) * (realTotientLowCount n t : ℝ)) + 1 / 12500 := by
  have hnpos : 0 < n := by omega
  have hfac := large_n_div_two_m_lt hn
  have hG0 : 0 ≤ (2 / (n : ℝ)) * (realTotientLowCount n t : ℝ) := by positivity
  rw [realTotientLowCount_normalization hnpos]
  by_cases hz : (2 / (n : ℝ)) * (realTotientLowCount n t : ℝ) = 0
  · rw [hz]
    norm_num
  · have hgpos := lt_of_le_of_ne hG0 (Ne.symm hz)
    have hmul := mul_lt_mul_of_pos_right hfac hgpos
    nlinarith

/-- The global sixth moment controls the exact normalized low-profile count. -/
theorem large_count_moment {n : ℕ} {t : ℝ} (hn : 200000 ≤ n) (ht : 0 < t) :
    (realTotientLowCount n t : ℝ) / (n / 6 : ℕ) < (66003 : ℝ) / 1000 * t ^ 6 := by
  have hnpos : 0 < n := by omega
  have hmoment := odd_totient_cdf_lt_twenty_two_real_uniform hnpos ht
  change (2 / (n : ℝ)) * (realTotientLowCount n t : ℝ) < 22 * t ^ 6 at hmoment
  have hfac := large_n_div_two_m_lt hn
  have hm : (0 : ℝ) < (n / 6 : ℕ) := by exact_mod_cast large_m_pos hn
  have hfpos : 0 < (n : ℝ) / (2 * (n / 6 : ℕ)) := by positivity
  have hp : 0 < t ^ 6 := pow_pos ht 6
  have hmul := mul_lt_mul_of_pos_left hmoment hfpos
  rw [realTotientLowCount_normalization hnpos]
  nlinarith

@[simp] theorem realTotientLowCount_zero (n : ℕ) : realTotientLowCount n 0 = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro v hv
  have hρ : (0 : ℝ) ≤ totientDensity v := by exact_mod_cast totientDensity_nonneg v
  exact not_lt.mpr hρ

/-- A real-profile rank certificate constructs one common decreasing order. -/
theorem exact_interval_of_real_profile_resources (n : ℕ) (ps : List ℕ)
    (hcert : ∀ b : ℕ, b ≤ halfOdds n - retainedOdds n →
      ∀ j : ℕ, 1 ≤ j → j ≤ maxHalfLength n →
      ∃ s : ℕ, s ≤ ps.length ∧ ∃ t : ℝ,
        2 * (realTotientLowCount n t - b) + signatureBudget s < j ∧
        ((∀ u ∈ oddUniverse n, ∀ v ∈ oddUniverse n, u ≠ v →
          divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
          t ≤ (totientDensity u : ℝ) → t ≤ (totientDensity v : ℝ) →
          b + j ≤ (rawCommon Nat.Coprime (evenUniverse n) u v).card) ∨
         (∀ u ∈ oddUniverse n, ∀ v ∈ oddUniverse n, u ≠ v →
          divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
          t ≤ (totientDensity u : ℝ) → t ≤ (totientDensity v : ℝ) →
          n - threshold n + maxHalfLength n + j ≤
            (rawCommon Nat.Coprime (Finset.Icc 1 n) u v).card))) :
    ∃ O : List ℕ, O.Nodup ∧ O.toFinset = oddUniverse n ∧
      ExactIntervalCertificate n n O ps := by
  classical
  obtain ⟨O, hO, hOset, hsorted, hprefix⟩ :=
    exists_profile_order_all_thresholds (fun v => (totientDensity v : ℝ)) (oddUniverse n)
  have hOlen : O.length = halfOdds n := by
    simpa only [hOset, oddUniverse_card] using (List.toFinset_card_of_nodup hO).symm
  refine ⟨O, hO, hOset, ?_⟩
  intro b hb j hj hjU
  obtain ⟨s, hs, t, hbudget, hres⟩ := hcert b hb j hj hjU
  let R := realTotientLowCount n t
  let p := halfOdds n - R
  have hR : R ≤ halfOdds n := by
    have h := Finset.card_le_card
      (Finset.filter_subset (fun v => (totientDensity v : ℝ) < t) (oddUniverse n))
    simpa only [oddUniverse_card, R, realTotientLowCount, lowProfileCount] using h
  have hP : orderPrefix O p =
      (oddUniverse n).filter (fun v => t ≤ (totientDensity v : ℝ)) := by
    simpa only [hOlen, realTotientLowCount, lowProfileCount, R, p] using (hprefix t).2.1
  refine ⟨s, hs, p, Nat.sub_le _ _, ?_, ?_⟩
  · change 2 * (halfOdds n - p - b) + signatureBudget s < j
    change 2 * (R - b) + signatureBudget s < j at hbudget
    dsimp [p]
    omega
  · rcases hres with he | hw
    · left
      intro u hu v hv hne hcode
      rw [hP] at hu hv
      obtain ⟨hu, htu⟩ := Finset.mem_filter.mp hu
      obtain ⟨hv, htv⟩ := Finset.mem_filter.mp hv
      exact he u hu v hv hne hcode htu htv
    · right
      intro u hu v hv hne hcode
      rw [hP] at hu hv
      obtain ⟨hu, htu⟩ := Finset.mem_filter.mp hu
      obtain ⟨hv, htv⟩ := Finset.mem_filter.mp hv
      exact hw u hu v hv hne hcode htu htv

/-- The sixth moment alone settles the lower-threshold half of the large-rank case. -/
theorem large_rank_low_threshold_budget {n b j : ℕ} (hn : 200000 ≤ n)
    (hj : 1 ≤ j) (hjm : j ≤ n / 6)
    (hx : (1 : ℝ) / 20 ≤ (j : ℝ) / (n / 6 : ℕ))
    (ht : largeRankThreshold ((b : ℝ) / (n / 6 : ℕ)) ((j : ℝ) / (n / 6 : ℕ))
      (((3 : ℝ) / 2 * Real.sqrt n + 2) / (n / 6 : ℕ)) < (10 : ℝ) / 27) :
    2 * (realTotientLowCount n (largeRankThreshold
      ((b : ℝ) / (n / 6 : ℕ)) ((j : ℝ) / (n / 6 : ℕ))
      (((3 : ℝ) / 2 * Real.sqrt n + 2) / (n / 6 : ℕ))) - b) +
      signatureBudget (uniformTailScale n) < j := by
  let m := n / 6
  let β : ℝ := (b : ℝ) / m
  let x : ℝ := (j : ℝ) / m
  let ε : ℝ := ((3 : ℝ) / 2 * Real.sqrt n + 2) / m
  have hm : (0 : ℝ) < m := by exact_mod_cast large_m_pos hn
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hm).mpr (by exact_mod_cast hjm)
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hε : ε < (101 : ℝ) / 5000 := large_discrepancy_div_m_lt hn
  have hthreshold := (largeRankThreshold_bounds hβ hx0 hx1 hε0 hε).1
  have hteq := largeRankThreshold_low_eq hx0.le hε0 ht
  have hinterval := largeRankThreshold_low_profile_interval hβ hx hε0 ht
  have hcount := large_count_moment hn hthreshold
  have hcoef := low_profile_moment_coefficient (show 0 < β + x + ε by linarith)
  have htrans := large_transition_div_m_lt hn
  have hbudget := low_profile_rank_budget hβ hx hε htrans hinterval.1 hinterval.2.le
    (hcount.trans (by rw [hteq]; exact hcoef))
  have hs : uniformTailScale n ≠ 0 := by
    have := uniformTailScale_ge_six (show 1024 < n by omega)
    omega
  have hnat := normalized_rank_budget_to_nat (large_m_pos hn) hbudget
  simpa only [signatureBudget, if_neg hs] using hnat

/-- The unstructured small-rank threshold has the exact cubic moment budget. -/
theorem small_rank_threshold_budget {n b j : ℕ} (hn : 200000 ≤ n)
    (hj : 1 ≤ j) (hx : (j : ℝ) / (n / 6 : ℕ) ≤ (1 : ℝ) / 20)
    (hβ : (b : ℝ) / (n / 6 : ℕ) < (1 : ℝ) / 10) :
    2 * (realTotientLowCount n
      (Real.sqrt ((7 : ℝ) / 20 * ((b : ℝ) / (n / 6 : ℕ) +
        (j : ℝ) / (n / 6 : ℕ)))) - b) + signatureBudget 0 < j := by
  let m := n / 6
  let β : ℝ := (b : ℝ) / m
  let x : ℝ := (j : ℝ) / m
  let t := Real.sqrt ((7 : ℝ) / 20 * (β + x))
  have hm : (0 : ℝ) < m := by exact_mod_cast large_m_pos hn
  have hβ0 : 0 ≤ β := by dsimp [β]; positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hz : 0 < β + x := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht2 : t ^ 2 = (7 : ℝ) / 20 * (β + x) := by
    exact Real.sq_sqrt (by positivity)
  have ht6 : t ^ 6 = ((7 : ℝ) / 20 * (β + x)) ^ 3 := by
    calc
      t ^ 6 = (t ^ 2) ^ 3 := by ring
      _ = _ := by rw [ht2]
  have hcount := large_count_moment hn ht
  rw [ht6] at hcount
  have hcoef := small_rank_moment_coefficient hz
  have hbudget := small_rank_cubic_budget hβ0 hx0 hx
    (show β + x < (3 : ℝ) / 20 by linarith) (hcount.trans hcoef)
  have hnat := normalized_rank_budget_to_nat (h := 0) (large_m_pos hn)
    (by simpa using hbudget)
  simpa [signatureBudget, t, β, x, m] using hnat

/-- The checked CDF and sixth moment settle every large-rank threshold. -/
theorem large_rank_threshold_budget {n b j : ℕ} (hn : 200000 ≤ n)
    (hj : 1 ≤ j) (hjm : j ≤ n / 6)
    (hx : (1 : ℝ) / 20 ≤ (j : ℝ) / (n / 6 : ℕ)) :
    2 * (realTotientLowCount n (largeRankThreshold
      ((b : ℝ) / (n / 6 : ℕ)) ((j : ℝ) / (n / 6 : ℕ))
      (((3 : ℝ) / 2 * Real.sqrt n + 2) / (n / 6 : ℕ))) - b) +
      signatureBudget (uniformTailScale n) < j := by
  let m := n / 6
  let β : ℝ := (b : ℝ) / m
  let x : ℝ := (j : ℝ) / m
  let ε : ℝ := ((3 : ℝ) / 2 * Real.sqrt n + 2) / m
  let t := largeRankThreshold β x ε
  by_cases htlow : t < (10 : ℝ) / 27
  · exact large_rank_low_threshold_budget hn hj hjm hx htlow
  have hm : (0 : ℝ) < m := by exact_mod_cast large_m_pos hn
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hm).mpr (by exact_mod_cast hjm)
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hε : ε < (101 : ℝ) / 5000 := large_discrepancy_div_m_lt hn
  have ht := largeRankThreshold_bounds hβ hx0 hx1 hε0 hε
  have hcdf := totientCdf_refined_high (n := n) (t := t) (by omega)
    (by dsimp [t] at *; linarith) (by dsimp [t] at *; linarith)
  have hG : totientCdf n t ≤ 1 := by dsimp [t] at *; linarith
  have hcount := large_count_of_cdf_le_one hn hG
  have hnorm := high_profile_normalized_count hcdf hcount
    (show t ≤ (β + x + ε) / ((27 : ℝ) / 10) from min_le_left _ _)
  have hbudget := high_profile_rank_budget hx hx1 hε (large_transition_div_m_lt hn) hnorm
  have hnat := normalized_rank_budget_to_nat (large_m_pos hn) hbudget
  have hs : uniformTailScale n ≠ 0 := by
    have := uniformTailScale_ge_six (show 1024 < n by omega)
    omega
  simpa only [signatureBudget, if_neg hs] using hnat

/-- Clipped missing-even ratios give an unstructured zero-transition budget. -/
theorem clipped_low_rank_threshold_budget {n b j : ℕ} (hn : 200000 ≤ n)
    (hj : 1 ≤ j) (hβ : (1 : ℝ) / 10 ≤ (b : ℝ) / (n / 6 : ℕ)) :
    2 * (realTotientLowCount n
      (Real.sqrt ((min ((b : ℝ) / (n / 6 : ℕ)) 2 + (9 : ℝ) / 125) / 3)) - b) +
      signatureBudget 0 < j := by
  let m := n / 6
  let β : ℝ := (b : ℝ) / m
  let β₀ : ℝ := min β 2
  let t := Real.sqrt ((β₀ + (9 : ℝ) / 125) / 3)
  have hm : (0 : ℝ) < m := by exact_mod_cast large_m_pos hn
  have hβ₀lo : (1 : ℝ) / 10 ≤ β₀ := le_min hβ (by norm_num)
  have hβ₀hi : β₀ ≤ 2 := min_le_right _ _
  have hcdf := totientCdf_refined_low (n := n) hn hβ₀lo (show β₀ ≤ (201 : ℝ) / 100 by linarith)
  have hG : totientCdf n t ≤ 1 := by linarith
  have hcount := large_count_of_cdf_le_one hn hG
  have hnorm := clipped_low_rank_normalized_count hcdf hcount
  have hlt := clipped_low_rank_profile_lt (min_le_left β 2) hnorm
  have hx0 : (0 : ℝ) < (j : ℝ) / m := by positivity
  have hbudget : 2 * max 0 ((realTotientLowCount n t : ℝ) / m - β) +
      (0 : ℝ) / m < (j : ℝ) / m := by
    rw [max_eq_left (by linarith)]
    simpa using hx0
  have hnat := normalized_rank_budget_to_nat (R := realTotientLowCount n t)
    (b := b) (h := 0) (j := j) (large_m_pos hn) (by simpa [β, m] using hbudget)
  simpa [signatureBudget, t, β₀, β, m] using hnat

/-- Every size at least two hundred thousand has an unconditional exact interval certificate.
The same descending totient order and full adaptive coordinate list serve every rank. -/
theorem largeN_exact_interval_certificate {n : ℕ} (hn : 200000 ≤ n) :
    ∃ O ps : List ℕ, O.Nodup ∧ O.toFinset = oddUniverse n ∧
      ExactIntervalCertificate n n O ps := by
  classical
  let ps := adaptiveTailCoordinates (uniformTailScale n)
  suffices h : ∃ O : List ℕ, O.Nodup ∧ O.toFinset = oddUniverse n ∧
      ExactIntervalCertificate n n O ps by
    obtain ⟨O, hO, hset, hc⟩ := h
    exact ⟨O, ps, hO, hset, hc⟩
  apply exact_interval_of_real_profile_resources n ps
  intro b hb j hj hjm
  change j ≤ n / 6 at hjm
  let m := n / 6
  let β : ℝ := (b : ℝ) / m
  let x : ℝ := (j : ℝ) / m
  let δ : ℝ := (3 : ℝ) / 2 * Real.sqrt n
  let ε : ℝ := (δ + 2) / m
  have hmN : 0 < m := large_m_pos hn
  have hm : (0 : ℝ) < m := by exact_mod_cast hmN
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hm).mpr (by exact_mod_cast hjm)
  have hε0 : 0 ≤ ε := by dsimp [ε, δ]; positivity
  have hε : ε < (101 : ℝ) / 5000 := large_discrepancy_div_m_lt hn
  have hmb : (m : ℝ) * β = b := by dsimp [β]; field_simp
  have hmj : (m : ℝ) * x = j := by dsimp [x]; field_simp
  have hmε : (m : ℝ) * ε = δ + 2 := by dsimp [ε]; field_simp
  by_cases hx : (1 : ℝ) / 20 ≤ x
  · let t := largeRankThreshold β x ε
    have ht := largeRankThreshold_bounds hβ hx0 hx1 hε0 hε
    refine ⟨uniformTailScale n, by simp [ps], t,
      large_rank_threshold_budget hn hj hjm hx, ?_⟩
    have hD : (n - threshold n + maxHalfLength n : ℕ) ≤ 3 * m + 2 :=
      resource_cost_le_three_m_add_two n
    have hres := largeRankThreshold_resource_target hmb hmj hmε
      (show ((n - threshold n + maxHalfLength n : ℕ) : ℝ) ≤ 3 * (m : ℝ) + 2 by
        exact_mod_cast hD)
    have htake : ps.take (uniformTailScale n) = ps :=
      List.take_of_length_le (by simp [ps])
    rcases hres with he | hw
    · left
      intro u hu v hv hne hcode htu htv
      obtain ⟨hui, huo⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvi, hvo⟩ := Finset.mem_filter.mp hv
      obtain ⟨hup, hun⟩ := Finset.mem_Icc.mp hui
      obtain ⟨hvp, hvn⟩ := Finset.mem_Icc.mp hvi
      rw [htake] at hcode
      have hraw := real_structured_resources (show 1024 < n by omega)
        hup hvp huo hvo hun hvn ht.1.le htu hcode
      have hlt : (b : ℝ) + j <
          ((rawCommon Nat.Coprime (evenUniverse n) u v).card : ℝ) := he.trans_lt hraw.1
      exact_mod_cast hlt.le
    · right
      intro u hu v hv hne hcode htu htv
      obtain ⟨hui, huo⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvi, hvo⟩ := Finset.mem_filter.mp hv
      obtain ⟨hup, hun⟩ := Finset.mem_Icc.mp hui
      obtain ⟨hvp, hvn⟩ := Finset.mem_Icc.mp hvi
      rw [htake] at hcode
      have hraw := real_structured_resources (show 1024 < n by omega)
        hup hvp huo hvo hun hvn ht.1.le htu hcode
      have hlt := hw.trans_lt hraw.2
      exact_mod_cast hlt.le
  · have hxsmall : x ≤ (1 : ℝ) / 20 := le_of_not_ge hx
    by_cases hβlarge : (1 : ℝ) / 10 ≤ β
    · let β₀ := min β 2
      let t := Real.sqrt ((β₀ + (9 : ℝ) / 125) / 3)
      have hβ₀lo : (1 : ℝ) / 10 ≤ β₀ := le_min hβlarge (by norm_num)
      have ht : 0 ≤ t := Real.sqrt_nonneg _
      have ht2 : t ^ 2 = (β₀ + (9 : ℝ) / 125) / 3 := Real.sq_sqrt (by positivity)
      refine ⟨0, Nat.zero_le _, t, clipped_low_rank_threshold_budget hn hj hβlarge, Or.inl ?_⟩
      have hδ : δ + 2 < (101 : ℝ) / 5000 * m := (div_lt_iff₀ hm).mp hε
      have hres := clipped_low_rank_resource_target hm.le hmb hmj hxsmall
        (clipped_beta_loss hn hb).2 hδ
      have hres' : (b : ℝ) + j < 3 * (m : ℝ) * t ^ 2 - δ := by
        have hs := congrArg (fun z : ℝ => 3 * (m : ℝ) * z) ht2
        nlinarith
      intro u hu v hv hne hcode htu htv
      obtain ⟨hui, huo⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvi, hvo⟩ := Finset.mem_filter.mp hv
      obtain ⟨hup, hun⟩ := Finset.mem_Icc.mp hui
      obtain ⟨hvp, hvn⟩ := Finset.mem_Icc.mp hvi
      have hraw := real_unstructured_resources hup hvp huo hvo hun hvn ht htu htv
      have hlt := hres'.trans hraw.1
      exact_mod_cast hlt.le
    · have hβsmall : β < (1 : ℝ) / 10 := lt_of_not_ge hβlarge
      by_cases hsum : (b : ℝ) + j ≤ 30 * Real.sqrt n
      · refine ⟨0, Nat.zero_le _, 0, ?_, Or.inl ?_⟩
        · simpa [signatureBudget] using (show 0 < j by omega)
        · intro u hu v hv hne hcode htu htv
          obtain ⟨hui, huo⟩ := Finset.mem_filter.mp hu
          obtain ⟨hvi, hvo⟩ := Finset.mem_filter.mp hv
          obtain ⟨hup, hun⟩ := Finset.mem_Icc.mp hui
          obtain ⟨hvp, hvn⟩ := Finset.mem_Icc.mp hvi
          have hraw := rawCommon_coprime_even_card_gt_thirty_sqrt hn hup hvp huo hvo hun hvn
          have hlt := hsum.trans_lt hraw
          exact_mod_cast hlt.le
      · let t := Real.sqrt ((7 : ℝ) / 20 * (β + x))
        have ht : 0 ≤ t := Real.sqrt_nonneg _
        have ht2 : t ^ 2 = (7 : ℝ) / 20 * (β + x) := Real.sq_sqrt (by positivity)
        refine ⟨0, Nat.zero_le _, t, small_rank_threshold_budget hn hj hxsmall hβsmall, Or.inl ?_⟩
        have hδ : δ < ((b : ℝ) + j) / 20 := by dsimp [δ]; linarith
        have hres := small_rank_resource_target hmb hmj ht2 hδ
        intro u hu v hv hne hcode htu htv
        obtain ⟨hui, huo⟩ := Finset.mem_filter.mp hu
        obtain ⟨hvi, hvo⟩ := Finset.mem_filter.mp hv
        obtain ⟨hup, hun⟩ := Finset.mem_Icc.mp hui
        obtain ⟨hvp, hvn⟩ := Finset.mem_Icc.mp hvi
        have hraw := real_unstructured_resources hup hvp huo hvo hun hvn ht htu htv
        have hlt := hres.trans hraw.1
        exact_mod_cast hlt.le

/-- The canonical odd-cycle conclusion throughout the analytic range. -/
theorem largeN_odd_cycle {n : ℕ} (hn : 200000 ≤ n)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  obtain ⟨O, ps, hO, hset, hc⟩ := largeN_exact_interval_certificate hn
  exact exact_interval_criterion_with_proved_endpoints (by omega) O ps hO hset hc
    le_rfl le_rfl A hA hdense hk hkn

/-- Part (i), in its canonical odd-length formulation, for every large ambient size. -/
theorem firstQuestion_largeN (n : ℕ) (hn : 200000 ≤ n)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hdense : n / 2 + n / 3 - n / 6 < A.card)
    (l : ℕ) (hl : Odd l) (h3 : 3 ≤ l) (hln : l ≤ n / 3 + 1) :
    l ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  obtain ⟨k, hk, hkn, rfl⟩ := (length_range_iff n l).mp ⟨hl, h3, hln⟩
  exact largeN_odd_cycle hn A hA hdense hk hkn

#print axioms firstQuestion_largeN
#print axioms largeN_exact_interval_certificate
#print axioms largeN_odd_cycle
end Erdos883Verified.Improved
