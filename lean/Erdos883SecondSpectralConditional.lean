import Erdos883SecondSpectralStability

namespace Erdos883.SecondSpectral

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oneBits (j : ι) : ι → Bool := fun i => decide (i = j)

def tensorSliceMass (p : ι → ℝ) (f : (ι → Bool) → ℝ)
    (j : ι) (b : Bool) : ℝ :=
  ∑ x : ι → Bool, tensorWeight p x * f x * (if x j = b then 1 else 0)

def tensorThreeMean (p : ι → ℝ) (f : (ι → Bool) → ℝ)
    (j : ι) (b : Bool) : ℝ :=
  if b then 3 * tensorSliceMass p f j true else
    (3 / 2) * tensorSliceMass p f j false

omit [DecidableEq ι] in
theorem primeBitSupport_mem (q : ι → ℕ) (hq : Function.Injective q)
    (s : ι → Bool) (i : ι) : q i ∈ primeBitSupport q s ↔ s i = true := by
  constructor
  · intro h
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp h
    have heq : k = i := hq hki
    subst k
    exact (Finset.mem_filter.mp hk).2
  · intro h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

 theorem primeBitSupport_eq_three (q : ι → ℕ) (hq : Function.Injective q)
    (j : ι) (hj : q j = 3) (s : ι → Bool) :
    primeBitSupport q s = {3} ↔ s = oneBits j := by
  constructor
  · intro h
    funext i
    have hi : s i = true ↔ i = j := by
      rw [← primeBitSupport_mem q hq s i, h, Finset.mem_singleton]
      exact ⟨fun hqi => hq (hqi.trans hj.symm), fun hij => by simpa [hij] using hj⟩
    by_cases hij : i = j
    · have hb := hi.mpr hij
      simp only [oneBits, hij, decide_true]
      simpa [hij] using hb
    · have hb : s i = false := Bool.eq_false_iff.mpr (fun ht => hij (hi.mp ht))
      simp [oneBits, hij, hb]
  · intro h
    subst s
    apply Finset.ext
    intro r
    simp only [primeBitSupport, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, oneBits, decide_eq_true_eq,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi, rfl⟩
      simpa [hi] using hj
    · intro hr
      exact ⟨j, rfl, hj.trans hr.symm⟩

omit [Fintype ι] in
@[simp] theorem oneBits_ne_zeroBits (j : ι) : oneBits j ≠ (zeroBits : ι → Bool) := by
  intro h
  have hj := congr_fun h j
  simp [oneBits, zeroBits] at hj

@[simp] theorem tensorBasis_oneBits (p : ι → ℝ) (j : ι) (x : ι → Bool) :
    tensorBasis p (oneBits j) x = centeredCoordinate (p j) (x j) := by
  rw [tensorBasis]
  rw [Finset.prod_eq_single j]
  · simp [oneBits, coordinateBasis]
  · intro i _ hij
    simp [oneBits, coordinateBasis, hij]
  · simp

@[simp] theorem tensorNorm_oneBits (p : ι → ℝ) (j : ι) :
    tensorNorm p (oneBits j) = (p j - 1) / (p j)^2 := by
  rw [tensorNorm]
  rw [Finset.prod_eq_single j]
  · simp [oneBits, coordinateNorm]
  · intro i _ hij
    simp [oneBits, coordinateNorm, hij]
  · simp

 theorem tensorSliceMass_partition (p : ι → ℝ) (f : (ι → Bool) → ℝ) (j : ι) :
    tensorSliceMass p f j false + tensorSliceMass p f j true = tensorMean p f := by
  rw [tensorSliceMass, tensorSliceMass, tensorMean, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases x j <;> simp

 theorem tensorThreeMean_mean (p : ι → ℝ) (f : (ι → Bool) → ℝ) (j : ι) :
    tensorMean p f = (2 / 3) * tensorThreeMean p f j false +
      (1 / 3) * tensorThreeMean p f j true := by
  rw [← tensorSliceMass_partition p f j]
  simp only [tensorThreeMean, Bool.false_eq_true, if_false, if_true]
  ring

 theorem tensorFourierCoefficient_three (p : ι → ℝ) (j : ι) (hj : p j = 3)
    (f : (ι → Bool) → ℝ) :
    tensorFourierCoefficient p f (oneBits j) =
      tensorThreeMean p f j true - tensorThreeMean p f j false := by
  rw [tensorFourierCoefficient, tensorNorm_oneBits, hj]
  simp only [tensorBasis_oneBits]
  have hnum : (∑ x : ι → Bool,
      tensorWeight p x * f x * centeredCoordinate 3 (x j)) =
      -(1 / 3) * tensorSliceMass p f j false +
        (2 / 3) * tensorSliceMass p f j true := by
    rw [tensorSliceMass, tensorSliceMass, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    cases x j <;> simp [centeredCoordinate] <;> ring
  rw [hj, hnum]
  simp only [tensorThreeMean, Bool.false_eq_true, if_false, if_true]
  ring

 theorem tensorResidual_decomposition (q : ι → ℕ) (hqi : Function.Injective q)
    (hq : ∀ i, 3 ≤ q i) (j : ι) (hj : q j = 3)
    (f : (ι → Bool) → ℝ) :
    tensorSecondMoment (fun i => (q i : ℝ)) f =
      (tensorMean (fun i => (q i : ℝ)) f)^2 +
        (2 / 9) * (tensorThreeMean (fun i => (q i : ℝ)) f j true -
          tensorThreeMean (fun i => (q i : ℝ)) f j false)^2 +
        tensorResidual q f := by
  let p : ι → ℝ := fun i => (q i : ℝ)
  let w : (ι → Bool) → ℝ := fun s =>
    (tensorFourierCoefficient p f s)^2 * tensorNorm p s
  have hp0 : ∀ i, p i ≠ 0 := by
    intro i
    have hh : 3 ≤ p i := by dsimp [p]; exact_mod_cast hq i
    linarith
  have hp1 : ∀ i, p i ≠ 1 := by
    intro i
    have hh : 3 ≤ p i := by dsimp [p]; exact_mod_cast hq i
    linarith
  have hpj : p j = 3 := by dsimp [p]; exact_mod_cast hj
  have hsum : (∑ s : ι → Bool, w s) =
      w zeroBits + w (oneBits j) + tensorResidual q f := by
    have hpnt : ∀ s : ι → Bool, w s =
        (if s = zeroBits then w s else 0) +
        (if s = oneBits j then w s else 0) +
        (if s ≠ zeroBits ∧ primeBitSupport q s ≠ {3} then w s else 0) := by
      intro s
      have h3iff := not_congr (primeBitSupport_eq_three q hqi j hj s)
      simp only [h3iff]
      by_cases h0 : s = zeroBits
      · subst s
        have hn : (zeroBits : ι → Bool) ≠ oneBits j := Ne.symm (oneBits_ne_zeroBits j)
        simp [hn]
      · by_cases h1 : s = oneBits j <;> simp [h0, h1]
    conv_lhs => arg 2; ext s; rw [hpnt s]
    simp only [Finset.sum_add_distrib]
    have hres : (∑ s : ι → Bool,
        if s ≠ zeroBits ∧ primeBitSupport q s ≠ {3} then w s else 0) =
        tensorResidual q f := by rw [tensorResidual, Finset.sum_filter]
    rw [hres]
    simp
  have hparseval := tensorFourier_parseval p hp0 hp1 f
  change tensorSecondMoment p f = _ at hparseval
  rw [hparseval]
  change (∑ s : ι → Bool, w s) = _
  rw [hsum]
  simp [w, tensorFourierCoefficient_three p j hpj f, hpj]
  ring

 theorem tensorThreeMean_conditional_defect (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, 3 ≤ q i)
    (j : ι) (hj : q j = 3) (f : (ι → Bool) → ℝ) :
    tensorFractionalDefect (fun i => (q i : ℝ)) f + tensorResidual q f =
      (2 / 3) * tensorThreeMean (fun i => (q i : ℝ)) f j false *
        (1 - tensorThreeMean (fun i => (q i : ℝ)) f j false) +
      (1 / 3) * tensorThreeMean (fun i => (q i : ℝ)) f j true *
        (1 - tensorThreeMean (fun i => (q i : ℝ)) f j true) := by
  rw [tensorFractionalDefect, tensorResidual_decomposition q hqi hq j hj f]
  rw [tensorThreeMean_mean _ f j]
  ring

 theorem tensorFourierCoefficient_const_oneBits (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (j : ι) :
    tensorFourierCoefficient p (fun _ => 1) (oneBits j) = 0 := by
  have horth := tensorBasis_orthogonal p hp0 zeroBits (oneBits j)
  have hn : (zeroBits : ι → Bool) ≠ oneBits j := Ne.symm (oneBits_ne_zeroBits j)
  simp only [hn, if_false, tensorBasis_zeroBits, mul_one] at horth
  simp only [tensorFourierCoefficient, mul_one, horth, zero_div]

 theorem tensorThreeMean_const (p : ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (j : ι) (hj : p j = 3) (b : Bool) :
    tensorThreeMean p (fun _ => 1) j b = 1 := by
  have hmean := tensorThreeMean_mean p (fun _ => 1) j
  have hmean1 : tensorMean p (fun _ => 1) = 1 := by
    simp only [tensorMean, mul_one]
    exact tensorWeight_sum p hp0
  rw [hmean1] at hmean
  have hdiff := tensorFourierCoefficient_three p j hj (fun _ => 1)
  rw [tensorFourierCoefficient_const_oneBits p hp0 j] at hdiff
  cases b <;> linarith

 theorem tensorThreeMean_bounds (p : ι → ℝ) (hp : ∀ i, 1 ≤ p i)
    (hp0 : ∀ i, p i ≠ 0) (j : ι) (hj : p j = 3)
    (f : (ι → Bool) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (b : Bool) :
    0 ≤ tensorThreeMean p f j b ∧ tensorThreeMean p f j b ≤ 1 := by
  have hnonneg : ∀ b, 0 ≤ tensorSliceMass p f j b := by
    intro b
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (mul_nonneg (tensorWeight_nonneg p hp x) (hf x).1)
      (by split_ifs <;> norm_num)
  have hle : ∀ b, tensorSliceMass p f j b ≤ tensorSliceMass p (fun _ => 1) j b := by
    intro b
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_left (hf x).2 (tensorWeight_nonneg p hp x)
    · split_ifs <;> norm_num
  have hlemean : tensorThreeMean p f j b ≤ tensorThreeMean p (fun _ => 1) j b := by
    cases b <;> simp only [tensorThreeMean, Bool.false_eq_true, if_false, if_true]
    · exact mul_le_mul_of_nonneg_left (hle false) (by norm_num)
    · exact mul_le_mul_of_nonneg_left (hle true) (by norm_num)
  constructor
  · cases b <;> simp only [tensorThreeMean, Bool.false_eq_true, if_false, if_true]
    · exact mul_nonneg (by norm_num) (hnonneg false)
    · exact mul_nonneg (by norm_num) (hnonneg true)
  · rw [tensorThreeMean_const p hp0 j hj b] at hlemean
    exact hlemean

/-- The natural odd-signature mass with the prime-3 bit absent, multiplied by
the parity probability 1/2. All spectral and conditional-moment premises in
the scalar stability estimate have now been proved from the actual function. -/
 theorem tensorOutsideMass_small (q : ι → ℕ) (hqi : Function.Injective q)
    (hq : ∀ i, (q i).Prime ∧ 3 ≤ q i) (j : ι) (hj : q j = 3)
    (f : (ι → Bool) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (eps : ℝ) (heps : 0 ≤ eps) (heps_small : eps ≤ 1 / 12)
    (hmu : 1 / 3 - 2 * eps ≤ tensorMean (fun i => (q i : ℝ)) f)
    (hsmall : tensorPairCorrelation (fun i => (q i : ℝ)) f f + eps ≤ 1 / 48) :
    tensorSliceMass (fun i => (q i : ℝ)) f j false / 2 ≤
      8 * (tensorPairCorrelation (fun i => (q i : ℝ)) f f + eps) := by
  let p : ι → ℝ := fun i => (q i : ℝ)
  have hp : ∀ i, 1 ≤ p i := by
    intro i
    have hh : 3 ≤ p i := by dsimp [p]; exact_mod_cast (hq i).2
    linarith
  have hp0 : ∀ i, p i ≠ 0 := by intro i; linarith [hp i]
  have hpj : p j = 3 := by dsimp [p]; exact_mod_cast hj
  have ha0 := tensorThreeMean_bounds p hp hp0 j hpj f hf false
  have ha1 := tensorThreeMean_bounds p hp hp0 j hpj f hf true
  have hI := tensorFractionalDefect_nonneg p hp f hf
  have hR := tensorResidual_nonneg q (fun i => (hq i).2) f
  have hgap := tensorPairCorrelation_spectral_gap q hqi hq f
  have hcond := tensorThreeMean_conditional_defect q hqi (fun i => (hq i).2) j hj f
  have hout := Erdos883Second.Stability.outside_mass_small heps heps_small hmu hI hR
    hgap hsmall ha0.1 ha1.1 ha1.2 (tensorThreeMean_mean p f j) rfl hcond
  change tensorThreeMean p f j false / 3 ≤ _ at hout
  simp only [tensorThreeMean, Bool.false_eq_true, if_false] at hout
  change tensorSliceMass p f j false / 2 ≤ _
  nlinarith [hout]

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorThreeMean_conditional_defect
#print axioms Erdos883.SecondSpectral.tensorOutsideMass_small


