import Erdos883RelationResources
import Erdos883ParityCounts
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos883Verified

/-- Coprimality with an lcm is precisely simultaneous coprimality. -/
theorem coprime_lcm_iff (w u v : ℕ) :
    Nat.Coprime w (Nat.lcm u v) ↔ Nat.Coprime w u ∧ Nat.Coprime w v := by
  constructor
  · intro h
    exact ⟨h.of_dvd_right (Nat.dvd_lcm_left u v),
      h.of_dvd_right (Nat.dvd_lcm_right u v)⟩
  · rintro ⟨hu, hv⟩
    exact (hu.mul_right hv).of_dvd_right (Nat.lcm_dvd_mul u v)

/-- Multiplication by two preserves coprimality with odd endpoints. -/
theorem coprime_two_mul_iff_of_odd (w : ℕ) {u : ℕ} (hu : Odd u) :
    Nat.Coprime (2 * w) u ↔ Nat.Coprime w u := by
  rw [Nat.coprime_mul_iff_left]
  exact and_iff_right hu.coprime_two_left

/-- All positive interval witnesses, including the possible witness 1. -/
theorem rawCommon_coprime_Icc_eq (L u v : ℕ) :
    rawCommon Nat.Coprime (Finset.Icc 1 L) u v =
      (Finset.Icc 1 L).filter (fun w => Nat.Coprime w (Nat.lcm u v)) := by
  ext w
  simp only [rawCommon, Finset.mem_filter, coprime_lcm_iff]

/-- The positive even interval is the doubling image of the positive half interval. -/
theorem evenUniverse_eq_image_Icc (L : ℕ) :
    evenUniverse L = (Finset.Icc 1 (L / 2)).image (fun w => 2 * w) := by
  ext w
  simp only [evenUniverse, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, ⟨k, hk⟩⟩
    exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨k, ⟨hlo, hhi⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k, by omega⟩⟩

/-- Doubling identifies the even raw common-neighbor pool with positive
integers up to L/2 coprime to the lcm of the two odd endpoints. -/
theorem rawCommon_coprime_even_eq_image (L : ℕ) {u v : ℕ}
    (hu : Odd u) (hv : Odd v) :
    rawCommon Nat.Coprime (evenUniverse L) u v =
      ((Finset.Icc 1 (L / 2)).filter
        (fun w => Nat.Coprime w (Nat.lcm u v))).image (fun w => 2 * w) := by
  ext w
  rw [rawCommon, evenUniverse_eq_image_Icc]
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hku, hkv⟩
    refine ⟨k, ⟨hk, (coprime_lcm_iff k u v).mpr ⟨?_, ?_⟩⟩, rfl⟩
    · exact (coprime_two_mul_iff_of_odd k hu).mp hku
    · exact (coprime_two_mul_iff_of_odd k hv).mp hkv
  · rintro ⟨k, ⟨hk, hcop⟩, rfl⟩
    rcases (coprime_lcm_iff k u v).mp hcop with ⟨hku, hkv⟩
    exact ⟨⟨k, hk, rfl⟩, (coprime_two_mul_iff_of_odd k hu).mpr hku,
      (coprime_two_mul_iff_of_odd k hv).mpr hkv⟩

/-- Exact even-pool count; no asymptotic or discrepancy hypothesis is used. -/
theorem rawCommon_coprime_even_card (L : ℕ) {u v : ℕ}
    (hu : Odd u) (hv : Odd v) :
    (rawCommon Nat.Coprime (evenUniverse L) u v).card =
      ((Finset.Icc 1 (L / 2)).filter
        (fun w => Nat.Coprime w (Nat.lcm u v))).card := by
  rw [rawCommon_coprime_even_eq_image L hu hv]
  apply Finset.card_image_of_injective
  intro a b h
  dsimp at h
  omega

/-- Exact full-pool count. The interval starts at 1, not at 2. -/
theorem rawCommon_coprime_Icc_card (L u v : ℕ) :
    (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card =
      ((Finset.Icc 1 L).filter (fun w => Nat.Coprime w (Nat.lcm u v))).card := by
  rw [rawCommon_coprime_Icc_eq]

/-- Positive-prefix count, with 1 included whenever the interval is nonempty. -/
def coprimePrefixCount (L d : ℕ) : ℕ :=
  ((Finset.Icc 1 L).filter (fun w => Nat.Coprime w d)).card

/-- Splitting a positive prefix at an arbitrary nonnegative endpoint. -/
theorem coprimePrefixCount_add (a b d : ℕ) :
    coprimePrefixCount (a + b) d = coprimePrefixCount a d +
      ((Finset.Icc (a + 1) (a + b)).filter (fun w => Nat.Coprime w d)).card := by
  have hunion :
      (Finset.Icc 1 (a + b)).filter (fun w => Nat.Coprime w d) =
        (Finset.Icc 1 a).filter (fun w => Nat.Coprime w d) ∪
        (Finset.Icc (a + 1) (a + b)).filter (fun w => Nat.Coprime w d) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hcop⟩
      by_cases hwa : w ≤ a
      · exact Or.inl ⟨⟨hlo, hwa⟩, hcop⟩
      · exact Or.inr ⟨⟨by omega, hhi⟩, hcop⟩
    · rintro (⟨⟨hlo, hhi⟩, hcop⟩ | ⟨⟨hlo, hhi⟩, hcop⟩)
      · exact ⟨⟨hlo, by omega⟩, hcop⟩
      · exact ⟨⟨by omega, hhi⟩, hcop⟩
  have hdisj : Disjoint
      ((Finset.Icc 1 a).filter (fun w => Nat.Coprime w d))
      ((Finset.Icc (a + 1) (a + b)).filter (fun w => Nat.Coprime w d)) := by
    apply Finset.disjoint_left.mpr
    intro w hw1 hw2
    have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hw1).1).2
    have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hw2).1).1
    omega
  unfold coprimePrefixCount
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- Translation by a multiple of the modulus preserves the exact coprime filter. -/
theorem coprime_Icc_shift_eq_image (q r d : ℕ) :
    (Finset.Icc (q * d + 1) (q * d + r)).filter (fun w => Nat.Coprime w d) =
      ((Finset.Icc 1 r).filter (fun w => Nat.Coprime w d)).image
        (fun w => q * d + w) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hcop⟩
    refine ⟨w - q * d, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    have heq : q * d + (w - q * d) = w := by omega
    exact (Nat.coprime_mul_right_add_left (w - q * d) d q).mp (heq.symm ▸ hcop)
  · rintro ⟨k, ⟨⟨hlo, hhi⟩, hcop⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, (Nat.coprime_mul_right_add_left k d q).mpr hcop⟩

/-- Every translated prefix after a whole number of periods has the same count. -/
theorem coprime_Icc_shift_card (q r d : ℕ) :
    ((Finset.Icc (q * d + 1) (q * d + r)).filter
      (fun w => Nat.Coprime w d)).card = coprimePrefixCount r d := by
  rw [coprime_Icc_shift_eq_image]
  apply Finset.card_image_of_injective
  intro a b h
  dsimp at h
  omega

/-- Exact splitting at a whole number of periods. -/
theorem coprimePrefixCount_mul_add (q r d : ℕ) :
    coprimePrefixCount (q * d + r) d =
      coprimePrefixCount (q * d) d + coprimePrefixCount r d := by
  rw [coprimePrefixCount_add, coprime_Icc_shift_card]

/-- Exact count over any whole number of periods, including the zero modulus. -/
theorem coprimePrefixCount_mul (q d : ℕ) :
    coprimePrefixCount (q * d) d = q * coprimePrefixCount d d := by
  induction q with
  | zero => simp [coprimePrefixCount]
  | succ q ih =>
    rw [Nat.succ_mul, coprimePrefixCount_mul_add, ih, Nat.succ_mul]

/-- The full prefix consists of complete periods and one exact remainder.
This identity remains valid for d = 0 under natural-number division conventions. -/
theorem coprimePrefixCount_div_mod (L d : ℕ) :
    coprimePrefixCount L d =
      L / d * coprimePrefixCount d d + coprimePrefixCount (L % d) d := by
  have h := coprimePrefixCount_mul_add (L / d) (L % d) d
  rw [coprimePrefixCount_mul] at h
  have heq : L / d * d + L % d = L := Nat.div_add_mod' L d
  simpa only [heq] using h

/-- The remainder has at most its interval length many witnesses. -/
theorem coprimePrefixCount_le (L d : ℕ) : coprimePrefixCount L d ≤ L := by
  calc
    coprimePrefixCount L d ≤ (Finset.Icc 1 L).card := Finset.card_filter_le _ _
    _ = L := by simp

/-- Certified lower bound from complete periods only. -/
theorem coprimePrefixCount_complete_periods_le (L d : ℕ) :
    L / d * coprimePrefixCount d d ≤ coprimePrefixCount L d := by
  rw [coprimePrefixCount_div_mod L d]
  exact Nat.le_add_right _ _

/-- Certified upper bound retaining the modulus-dependent remainder length. -/
theorem coprimePrefixCount_le_complete_periods_add_mod (L d : ℕ) :
    coprimePrefixCount L d ≤ L / d * coprimePrefixCount d d + L % d := by
  rw [coprimePrefixCount_div_mod L d]
  exact Nat.add_le_add_left (coprimePrefixCount_le (L % d) d) _

/-- Exact periodic formula for the common-coprime full pool. -/
theorem rawCommon_coprime_Icc_card_div_mod (L u v : ℕ) :
    (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card =
      L / Nat.lcm u v * coprimePrefixCount (Nat.lcm u v) (Nat.lcm u v) +
        coprimePrefixCount (L % Nat.lcm u v) (Nat.lcm u v) := by
  rw [rawCommon_coprime_Icc_card]
  exact coprimePrefixCount_div_mod L (Nat.lcm u v)

/-- Exact periodic formula for the common-coprime even pool. -/
theorem rawCommon_coprime_even_card_div_mod (L : ℕ) {u v : ℕ}
    (hu : Odd u) (hv : Odd v) :
    (rawCommon Nat.Coprime (evenUniverse L) u v).card =
      (L / 2) / Nat.lcm u v * coprimePrefixCount (Nat.lcm u v) (Nat.lcm u v) +
        coprimePrefixCount ((L / 2) % Nat.lcm u v) (Nat.lcm u v) := by
  rw [rawCommon_coprime_even_card L hu hv]
  exact coprimePrefixCount_div_mod (L / 2) (Nat.lcm u v)

/-- The endpoint 1 is a full-pool witness even when it is an endpoint itself.
Removing simple-graph loops is a later operation, after skeleton deletion. -/
theorem one_mem_rawCommon_coprime_Icc {L : ℕ} (hL : 1 ≤ L) (u v : ℕ) :
    1 ∈ rawCommon Nat.Coprime (Finset.Icc 1 L) u v := by
  simp [rawCommon, hL]

#print axioms coprime_lcm_iff
#print axioms coprime_two_mul_iff_of_odd
#print axioms rawCommon_coprime_Icc_eq
#print axioms evenUniverse_eq_image_Icc
#print axioms rawCommon_coprime_even_eq_image
#print axioms rawCommon_coprime_even_card
#print axioms rawCommon_coprime_Icc_card

#print axioms coprimePrefixCount
#print axioms coprimePrefixCount_add
#print axioms coprime_Icc_shift_eq_image
#print axioms coprime_Icc_shift_card
#print axioms coprimePrefixCount_mul_add
#print axioms coprimePrefixCount_mul
#print axioms coprimePrefixCount_div_mod
#print axioms coprimePrefixCount_le
#print axioms coprimePrefixCount_complete_periods_le
#print axioms coprimePrefixCount_le_complete_periods_add_mod

#print axioms rawCommon_coprime_Icc_card_div_mod
#print axioms rawCommon_coprime_even_card_div_mod
#print axioms one_mem_rawCommon_coprime_Icc

end Erdos883Verified
