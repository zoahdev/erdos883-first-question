import Erdos883AdaptiveHistogram
import Erdos883SharpTail
import Erdos883NumericDegrees

namespace Erdos883Verified

def sharpDensityLower (c d : ℕ) (z : ℚ) : ℚ := max (z^2) (z * ((c : ℚ)/d))
def sharpDegree (scale W c d : ℕ) (z : ℚ) : ℕ :=
  ⌊(scale : ℚ) * sharpDensityLower c d z - coprimeDiscrepancyError W⌋₊

/-- A small finite certificate for an exact primorial tail factor. -/
def SharpTailCertificate (U : ℕ) (ps : List ℕ) (c d : ℕ) : Prop :=
  0 < d ∧ ∃ (Q : Finset ℕ) (q : ℕ),
    2 ≤ q ∧ (∀ x ∈ Q, 2 ≤ x ∧ x ≤ q) ∧
    (∀ r ∈ Finset.range q, r.Prime → r % 2 = 1 → r ∈ ps ∨ r ∈ Q) ∧
    U < q * (∏ x ∈ Q, x) ∧
    (c : ℚ)/d = ∏ x ∈ Q, (1 - (x : ℚ)⁻¹)

theorem sharpDensityLower_le_lcm {u v U c d : ℕ} {ps : List ℕ} {z : ℚ}
    (htail : SharpTailCertificate U ps c d)
    (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v) (hvU : v ≤ U)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v)
    (hz : 0 ≤ z) (hzu : z ≤ totientDensity u) (hzv : z ≤ totientDensity v) :
    sharpDensityLower c d z ≤ totientDensity (Nat.lcm u v) := by
  rcases htail with ⟨hd, Q, q, hq, hQ, hcover, hbudget, heta⟩
  apply max_le
  · exact totientDensity_lcm_ge_sq hu hv hz hzu hzv
  · have h := totientDensity_lcm_ge_finite_signature_sharpTail Q hu hv hvodd hvU
      hq (fun x hx => (hQ x hx).1) (fun x hx => (hQ x hx).2) hcover hcode hbudget
    rw [← heta] at h
    exact (mul_le_mul_of_nonneg_right hzu (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans h

theorem sharpDegree_mono (scale W c d : ℕ) {x y : ℚ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : sharpDegree scale W c d x ≤ sharpDegree scale W c d y := by
  apply Nat.floor_mono
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg scale)
  exact max_le_max (pow_le_pow_left₀ hx hxy 2)
    (mul_le_mul_of_nonneg_right hxy (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

theorem coreNumericDegree_eq_sharpDegree (scale W c d a b : ℕ)
    (hb : 0 < b) (hd : 0 < d) :
    coreNumericDegree scale W c d a b = sharpDegree scale W c d ((a : ℚ)/b) :=
  coreNumericDegree_eq_floor scale W c d a b hb hd

theorem sharp_profile_degree_bounds (L U W : ℕ) (ps : List ℕ) (c d : ℕ → ℕ)
    (htail : ∀ s ≤ ps.length, SharpTailCertificate U (ps.take s) (c s) (d s))
    (hW : ∀ u ∈ oddUniverse U, ∀ v ∈ oddUniverse U,
      (Nat.lcm u v).primeFactors.card ≤ W) :
    ProfileDegreeBounds totientDensity (fun z : ℚ => 0 ≤ z ∧ z ≤ 1) L U ps
      (fun s z => sharpDegree (L/2) W (c s) (d s) z)
      (fun s z => sharpDegree L W (c s) (d s) z) := by
  intro s hs z hz u huU v hvU _hne hcode hzu hzv
  rcases Finset.mem_filter.mp huU with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hvU with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU'⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU'⟩
  have hlow := sharpDensityLower_le_lcm (htail s hs) hu hv hvodd hvU' hcode hz.1 hzu hzv
  have hw := hW u (Finset.mem_filter.mpr ⟨huI, huodd⟩)
    v (Finset.mem_filter.mpr ⟨hvI, hvodd⟩)
  constructor
  · apply Nat.floor_le_of_le
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg (L/2))) _).trans
      (rawCommon_coprime_even_card_ge_density_sub_error_of_card_le L hu hv huodd hvodd hw)
  · apply Nat.floor_le_of_le
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg L)) _).trans
      (rawCommon_coprime_Icc_card_ge_density_sub_error_of_card_le L hu hv hw)

theorem sharp_histogram_interval_sound {L U : ℕ} (hL : 6 ≤ L)
    (W : ℕ) (ps : List ℕ) (c d : ℕ → ℕ)
    (htail : ∀ s ≤ ps.length, SharpTailCertificate U (ps.take s) (c s) (d s))
    (hW : ∀ u ∈ oddUniverse U, ∀ v ∈ oddUniverse U,
      (Nat.lcm u v).primeFactors.card ≤ W)
    (hcert : DegreeIntervalCertificate U ps
      (fun s v => sharpDegree (L/2) W (c s) (d s) (totientDensity v))
      (fun s v => sharpDegree L W (c s) (d s) (totientDensity v)))
    {n : ℕ} (hLn : L ≤ n) (hnU : n ≤ U)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2*k+1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  have hmono : DegreeProfileMonotone totientDensity U ps
      (fun s v => sharpDegree (L/2) W (c s) (d s) (totientDensity v))
      (fun s v => sharpDegree L W (c s) (d s) (totientDensity v)) := by
    intro s hs u hu v hv hprofile
    exact ⟨sharpDegree_mono _ _ _ _ (totientDensity_nonneg u) hprofile,
      sharpDegree_mono _ _ _ _ (totientDensity_nonneg u) hprofile⟩
  have hdegree := vertexDegreeBounds_of_profileDegreeBounds totientDensity
    (fun z : ℚ => 0 ≤ z ∧ z ≤ 1) L U ps _ _
    (fun v _ => ⟨totientDensity_nonneg v, totientDensity_le_one v⟩)
    (sharp_profile_degree_bounds L U W ps c d htail hW)
  exact degree_interval_criterion_sound totientDensity hL ps _ _ hmono hdegree hcert
    hLn hnU A hA hdense hk hkn

#print axioms sharpDensityLower_le_lcm
#print axioms sharpDegree_mono
#print axioms coreNumericDegree_eq_sharpDegree
#print axioms sharp_profile_degree_bounds
#print axioms sharp_histogram_interval_sound
end Erdos883Verified
