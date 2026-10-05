import Erdos883AdaptiveDegrees
import Erdos883DegreeCriterion

namespace Erdos883Verified

/-- Threshold degree bounds also certify each endpoint's own profile degree. -/
theorem vertexDegreeBounds_of_profileDegreeBounds {β : Type*} [LinearOrder β]
    (profile : ℕ → β) (valid : β → Prop) (L U : ℕ) (ps : List ℕ)
    (E R : ℕ → β → ℕ)
    (hvalid : ∀ v ∈ oddUniverse U, valid (profile v))
    (hdegree : ProfileDegreeBounds profile valid L U ps E R) :
    VertexDegreeBounds L U ps
      (fun s v => E s (profile v)) (fun s v => R s (profile v)) := by
  intro s hs K u hu v hv hne heq
  rcases le_total (profile u) (profile v) with h | h
  · have hg := hdegree s hs (profile u) (hvalid u hu) u hu v hv hne heq le_rfl h
    exact ⟨fun hKu _ => hKu.trans hg.1, fun hKu _ => hKu.trans hg.2⟩
  · have hg := hdegree s hs (profile v) (hvalid v hv) u hu v hv hne heq h le_rfl
    exact ⟨fun _ hKv => hKv.trans hg.1, fun _ hKv => hKv.trans hg.2⟩

theorem adaptiveDensityLower_mono {U p : ℕ} (hp : 2 ≤ p) {x y : ℚ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    adaptiveDensityLower U p x ≤ adaptiveDensityLower U p y := by
  apply max_le_max
  · exact pow_le_pow_left₀ hx hxy 2
  · exact mul_le_mul_of_nonneg_right hxy
      (pow_nonneg (thresholdFactor_mem_unitInterval hp).1 _)

theorem adaptiveDegree_mono (scale U W : ℕ) {p : ℕ} (hp : 2 ≤ p) {x y : ℚ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    adaptiveDegree scale U W p x ≤ adaptiveDegree scale U W p y := by
  apply Nat.floor_mono
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left (adaptiveDensityLower_mono hp hx hxy) (Nat.cast_nonneg scale)) _

/-- The candidate's adaptive lower-degree families are sorted by one totient profile order. -/
theorem adaptive_degree_profile_monotone (L U W : ℕ) (ps : List ℕ) (next : ℕ → ℕ)
    (hnext : ∀ s ≤ ps.length, 2 ≤ next s) :
    DegreeProfileMonotone totientDensity U ps
      (fun s v => adaptiveDegree (L / 2) U W (next s) (totientDensity v))
      (fun s v => adaptiveDegree L U W (next s) (totientDensity v)) := by
  intro s hs u _hu v _hv hprofile
  exact ⟨adaptiveDegree_mono _ _ _ (hnext s hs) (totientDensity_nonneg u) hprofile,
    adaptiveDegree_mono _ _ _ (hnext s hs) (totientDensity_nonneg u) hprofile⟩

/-- An adaptive degree-histogram certificate yields every required canonical cycle.
The remaining inputs are explicit finite prime coverage/support and histogram data. -/
theorem adaptive_histogram_interval_sound {L U : ℕ} (hL : 6 ≤ L)
    (W : ℕ) (ps : List ℕ) (next : ℕ → ℕ)
    (hnext : ∀ s ≤ ps.length, 2 ≤ next s)
    (hcover : ∀ s ≤ ps.length, ∀ q, q.Prime → q ≠ 2 → q < next s → q ∈ ps.take s)
    (hW : ∀ u ∈ oddUniverse U, ∀ v ∈ oddUniverse U,
      (Nat.lcm u v).primeFactors.card ≤ W)
    (hcert : DegreeIntervalCertificate U ps
      (fun s v => adaptiveDegree (L / 2) U W (next s) (totientDensity v))
      (fun s v => adaptiveDegree L U W (next s) (totientDensity v)))
    {n : ℕ} (hLn : L ≤ n) (hnU : n ≤ U)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  have hmono := adaptive_degree_profile_monotone L U W ps next hnext
  have hdegree := vertexDegreeBounds_of_profileDegreeBounds totientDensity
    (fun z : ℚ => 0 ≤ z ∧ z ≤ 1) L U ps _ _
    (fun v _ => ⟨totientDensity_nonneg v, totientDensity_le_one v⟩)
    (adaptive_profile_degree_bounds L U W ps next hnext hcover hW)
  exact degree_interval_criterion_sound totientDensity hL ps _ _ hmono hdegree hcert
    hLn hnU A hA hdense hk hkn

#print axioms vertexDegreeBounds_of_profileDegreeBounds
#print axioms adaptiveDensityLower_mono
#print axioms adaptiveDegree_mono
#print axioms adaptive_degree_profile_monotone
#print axioms adaptive_histogram_interval_sound
end Erdos883Verified
