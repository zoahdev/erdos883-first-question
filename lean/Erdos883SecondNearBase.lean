import Erdos883SecondCounts
import Erdos883SecondGoodProfiles
import Erdos883SecondQuestionFinsets

namespace Erdos883Second.Near

open Erdos883Verified

def standardUniverse (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun v => 2 ∣ v ∨ 3 ∣ v)

theorem standardUniverse_card (n : ℕ) :
    (standardUniverse n).card = n / 2 + n / 3 - n / 6 := by
  let F : ℕ → Finset ℕ := fun d => (Finset.Icc 1 n).filter (fun v => d ∣ v)
  have hu : standardUniverse n = F 2 ∪ F 3 := by
    ext v
    simp [standardUniverse, F, and_or_left]
  have hi : F 2 ∩ F 3 = F 6 := by
    ext v
    simp only [F, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hv, h2⟩, ⟨_, h3⟩⟩
      have h6 : Nat.lcm 2 3 ∣ v := Nat.lcm_dvd h2 h3
      norm_num at h6
      exact ⟨hv, h6⟩
    · rintro ⟨hv, h6⟩
      exact ⟨⟨hv, (by decide : 2 ∣ 6).trans h6⟩,
        ⟨hv, (by decide : 3 ∣ 6).trans h6⟩⟩
  rw [hu, Finset.card_union, hi]
  simp only [F, card_Icc_filter_dvd]

theorem standardUniverse_subset (n : ℕ) :
    standardUniverse n ⊆ Finset.Icc 1 n := Finset.filter_subset _ _

/-- The exact surplus, including all floor terms, pays for every missing
standard-universe vertex with a selected vertex outside that universe. -/
theorem missing_lt_extra {n : ℕ} {A : Finset ℕ}
    (hcard : n / 2 + n / 3 - n / 6 < A.card) :
    (standardUniverse n \ A).card < (A \ standardUniverse n).card := by
  have h1 := Finset.card_sdiff_add_card_inter A (standardUniverse n)
  have h2 := Finset.card_sdiff_add_card_inter (standardUniverse n) A
  rw [Finset.inter_comm (standardUniverse n) A, standardUniverse_card] at h2
  omega

theorem extra_mem_coprime_six {n a : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 n) (ha : a ∈ A \ standardUniverse n) :
    Nat.Coprime a 6 := by
  obtain ⟨haA, haU⟩ := Finset.mem_sdiff.mp ha
  have h2 : ¬ 2 ∣ a := by
    intro hd
    exact haU (Finset.mem_filter.mpr ⟨hA haA, Or.inl hd⟩)
  have h3 : ¬ 3 ∣ a := by
    intro hd
    exact haU (Finset.mem_filter.mpr ⟨hA haA, Or.inr hd⟩)
  have hc2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hc3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  exact hc2.mul_right hc3

/-- An entirely integer certificate converts the uniform support-power bound
into an explicit error budget. The premise must be checked; it is not an axiom. -/
theorem support_error_le_of_certificate {q n d r E : ℕ} (hq : 0 < q)
    (hqn : q ≤ n ^ d)
    (hcert : supportConstant r ^ r * n ^ d < (E + 1) ^ r) :
    2 ^ q.primeFactors.card ≤ E := by
  have hs := prime_support_power_bound_of_le (r := r) hq hqn
  by_contra he
  have hl : E + 1 ≤ 2 ^ q.primeFactors.card := by omega
  have hp := Nat.pow_le_pow_left hl r
  exact (not_lt_of_ge (hp.trans hs)) hcert

theorem totientDensity_finset_prod_ge (B : Finset ℕ)
    (hpos : ∀ b ∈ B, 0 < b) :
    (∏ b ∈ B, totientDensity b) ≤ totientDensity (∏ b ∈ B, b) := by
  classical
  induction B using Finset.induction_on with
  | empty => norm_num [totientDensity]
  | @insert b B hb ih =>
    have hbpos : 0 < b := hpos b (Finset.mem_insert_self _ _)
    have hBpos : ∀ x ∈ B, 0 < x := fun x hx => hpos x (Finset.mem_insert_of_mem hx)
    have hp : 0 < ∏ x ∈ B, x := Finset.prod_pos hBpos
    rw [Finset.prod_insert hb, Finset.prod_insert hb]
    calc
      _ ≤ totientDensity b * totientDensity (∏ x ∈ B, x) :=
        mul_le_mul_of_nonneg_left (ih hBpos) (totientDensity_nonneg b)
      _ ≤ _ := totientDensity_mul_ge hbpos hp

theorem product_density_ge_pow {B : Finset ℕ} {a : ℕ} {z : ℚ}
    (ha : 0 < a) (hpos : ∀ b ∈ B, 0 < b) (hz : 0 ≤ z)
    (haz : z ≤ totientDensity a) (hBz : ∀ b ∈ B, z ≤ totientDensity b) :
    z ^ (B.card + 1) ≤ totientDensity (a * ∏ b ∈ B, b) := by
  have hp : 0 < ∏ b ∈ B, b := Finset.prod_pos hpos
  have hB : z ^ B.card ≤ totientDensity (∏ b ∈ B, b) := by
    calc
      _ = ∏ b ∈ B, z := by simp
      _ ≤ ∏ b ∈ B, totientDensity b := Finset.prod_le_prod (fun _ _ => hz) hBz
      _ ≤ _ := totientDensity_finset_prod_ge B hpos
  calc
    _ = z * z ^ B.card := by rw [pow_succ]; ring
    _ ≤ totientDensity a * totientDensity (∏ b ∈ B, b) :=
      mul_le_mul haz hB (pow_nonneg hz _) (totientDensity_nonneg a)
    _ ≤ _ := totientDensity_mul_ge ha hp

theorem product_le_pow {B : Finset ℕ} {a n : ℕ}
    (han : a ≤ n) (hBn : ∀ b ∈ B, b ≤ n) :
    a * ∏ b ∈ B, b ≤ n ^ (B.card + 1) := by
  have hp : ∏ b ∈ B, b ≤ n ^ B.card := by
    calc
      _ ≤ ∏ b ∈ B, n := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hBn
      _ = _ := by simp
  calc
    _ ≤ n * n ^ B.card := Nat.mul_le_mul han hp
    _ = _ := by rw [pow_succ]; ring

def goodSelected (A S : Finset ℕ) (z : ℚ) : Finset ℕ :=
  (S ∩ A).filter (fun v => z ≤ totientDensity v)

/-- A finite deletion accounting lemma for the selected good-profile pool. -/
theorem candidate_card_le_good_missing_bad {n : ℕ} {A S : Finset ℕ} {z : ℚ}
    (hS : S ⊆ standardUniverse n) :
    S.card ≤ (goodSelected A S z).card + (standardUniverse n \ A).card +
      ((Finset.Icc 1 n).filter (fun v => totientDensity v < z)).card := by
  classical
  let bad := (Finset.Icc 1 n).filter (fun v => totientDensity v < z)
  have hs : S ⊆ (goodSelected A S z ∪ (standardUniverse n \ A)) ∪ bad := by
    intro v hv
    by_cases ha : v ∈ A
    · by_cases hzv : z ≤ totientDensity v
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hv, ha⟩, hzv⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨standardUniverse_subset n (hS hv), lt_of_not_ge hzv⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hS hv, ha⟩))
  calc
    _ ≤ ((goodSelected A S z ∪ (standardUniverse n \ A)) ∪ bad).card :=
      Finset.card_le_card hs
    _ ≤ (goodSelected A S z ∪ (standardUniverse n \ A)).card + bad.card :=
      Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _

#print axioms standardUniverse_card
#print axioms missing_lt_extra
#print axioms product_density_ge_pow
#print axioms candidate_card_le_good_missing_bad

end Erdos883Second.Near
