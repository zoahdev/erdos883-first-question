import Erdos883SecondSignaturePrefix

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators

def prefixCount (n : ℕ) (P : Finset ℕ) (s : Bits P) : ℕ :=
  Nat.count (fun x => signature P (x + 1) = s) n

def empiricalWeight (n : ℕ) (P : Finset ℕ) (s : Bits P) : ℝ :=
  (prefixCount n P s : ℝ) / n

def periodClass (P : Finset ℕ) (s : Bits P) : Finset (Fin (modulus P)) :=
  Finset.univ.filter (fun x => signature P x = s)

def prefixResidue (M : ℕ) (hM : 0 < M) (x : ℕ) : Fin M :=
  ⟨(x + 1) % M, Nat.mod_lt _ hM⟩

theorem signature_modulus (P : Finset ℕ) (x : ℕ) :
    signature P (x % modulus P) = signature P x := by
  funext p
  have hd : (p : ℕ) ∣ modulus P := Finset.dvd_prod_of_mem id p.property
  simp only [signature, Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd x hd]

theorem periodCount_card (P : Finset ℕ) (s : Bits P) :
    periodCount P s = (periodClass P s).card := by
  exact Fintype.card_of_subtype _ (fun x => by simp [periodClass])

theorem prefixCount_fiber (n : ℕ) (P : Finset ℕ) (hM : 0 < modulus P)
    (s : Bits P) :
    prefixCount n P s = ∑ r ∈ periodClass P s,
      residuePrefixCount n (modulus P) r := by
  have hh := Finset.sum_fiberwise_eq_sum_filter (Finset.range n) (periodClass P s)
    (prefixResidue (modulus P) hM) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at hh
  have hleft : (∑ r ∈ periodClass P s,
      {i ∈ Finset.range n | prefixResidue (modulus P) hM i = r}.card) =
      ∑ r ∈ periodClass P s, residuePrefixCount n (modulus P) r := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [residuePrefixCount, Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp [prefixResidue, Fin.ext_iff]
  have hright : {i ∈ Finset.range n |
      prefixResidue (modulus P) hM i ∈ periodClass P s}.card = prefixCount n P s := by
    rw [prefixCount, Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp [periodClass, prefixResidue, signature_modulus]
  exact (hleft.symm.trans (hh.trans hright)).symm

theorem periodCount_sum (P : Finset ℕ) : (∑ s : Bits P, periodCount P s) = modulus P := by
  simp only [periodCount_card, periodClass]
  have hh := Finset.sum_fiberwise (Finset.univ : Finset (Fin (modulus P)))
    (fun r => signature P r) (fun _ => (1 : ℕ))
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one, Finset.card_univ,
    Fintype.card_fin, Nat.cast_id] using hh

theorem prefixCount_error (n : ℕ) (P : Finset ℕ) (hM : 0 < modulus P)
    (s : Bits P) :
    |(prefixCount n P s : ℝ) - (n : ℝ) / modulus P * periodCount P s| ≤
      periodCount P s := by
  have he : (prefixCount n P s : ℝ) - (n : ℝ) / modulus P * periodCount P s =
      ∑ r ∈ periodClass P s,
        ((residuePrefixCount n (modulus P) r : ℝ) - (n : ℝ) / modulus P) := by
    rw [prefixCount_fiber n P hM s, periodCount_card, Nat.cast_sum,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ∑ r ∈ periodClass P s,
        |(residuePrefixCount n (modulus P) r : ℝ) - (n : ℝ) / modulus P| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ periodClass P s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      exact residuePrefixCount_error n (modulus P) r hM r.isLt
    _ = periodCount P s := by simp [periodCount_card]

theorem signature_frequency_l1 (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) :
    (∑ s : Bits P, |empiricalWeight n P s - productWeight P s|) ≤
      (modulus P : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 < modulus P := modulus_pos P hp
  have hMR : (0 : ℝ) < modulus P := by exact_mod_cast hM
  have hpoint (s : Bits P) :
      |empiricalWeight n P s - productWeight P s| ≤ (periodCount P s : ℝ) / n := by
    rw [← periodCount_div_modulus P hp hc s]
    have he : empiricalWeight n P s - (periodCount P s : ℝ) / modulus P =
        ((prefixCount n P s : ℝ) - (n : ℝ) / modulus P * periodCount P s) / n := by
      unfold empiricalWeight
      field_simp
    rw [he, abs_div, abs_of_pos hnR]
    exact div_le_div_of_nonneg_right (prefixCount_error n P hM s) hnR.le
  calc
    _ ≤ ∑ s : Bits P, (periodCount P s : ℝ) / n :=
      Finset.sum_le_sum (fun s _ => hpoint s)
    _ = (modulus P : ℝ) / n := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, periodCount_sum]

theorem prefixCount_card_Icc (n : ℕ) (P : Finset ℕ) (s : Bits P) :
    prefixCount n P s = ((Finset.Icc 1 n).filter (fun x => signature P x = s)).card := by
  rw [prefixCount, Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun x _ => x + 1)
  · intro x hx
    obtain ⟨hxn, hxs⟩ := Finset.mem_filter.mp hx
    have hxn' := Finset.mem_range.mp hxn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hxs⟩
  · intro x hx y hy he
    omega
  · intro y hy
    obtain ⟨hyn, hys⟩ := Finset.mem_filter.mp hy
    obtain ⟨hy1, hyn'⟩ := Finset.mem_Icc.mp hyn
    have he : y - 1 + 1 = y := by omega
    refine ⟨y - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, he⟩
    simpa only [he] using hys

theorem prefixCount_sum (n : ℕ) (P : Finset ℕ) :
    (∑ s : Bits P, prefixCount n P s) = n := by
  have hh := Finset.sum_fiberwise (Finset.range n) (fun x => signature P (x + 1))
    (fun _ => (1 : ℕ))
  simpa only [prefixCount, Nat.count_eq_card_filter_range, Finset.sum_const,
    nsmul_eq_mul, Nat.mul_one, Finset.card_range, Nat.cast_id] using hh

theorem empiricalWeight_nonneg (n : ℕ) (P : Finset ℕ) (s : Bits P) :
    0 ≤ empiricalWeight n P s := by unfold empiricalWeight; positivity

theorem empiricalWeight_sum (n : ℕ) (hn : 0 < n) (P : Finset ℕ) :
    (∑ s : Bits P, empiricalWeight n P s) = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [empiricalWeight, div_eq_mul_inv, ← Finset.sum_mul,
    ← Nat.cast_sum, prefixCount_sum, mul_inv_cancel₀ hnR]

theorem productWeight_nonneg (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) (s : Bits P) :
    0 ≤ productWeight P s := by
  rw [← periodCount_div_modulus P hp hc s]
  positivity

theorem productWeight_sum (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) :
    (∑ s : Bits P, productWeight P s) = 1 := by
  have hMR : (modulus P : ℝ) ≠ 0 := by exact_mod_cast (modulus_pos P hp).ne'
  simp_rw [← periodCount_div_modulus P hp hc]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum,
    periodCount_sum, mul_inv_cancel₀ hMR]

theorem signature_frequency_l1_primes (n : ℕ) (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hn : modulus P ≤ n) :
    (∑ s : Bits P, |empiricalWeight n P s - productWeight P s|) ≤
      (modulus P : ℝ) / n := by
  have hp0 : ∀ p ∈ P, 0 < p := fun p h => (hp p h).pos
  exact signature_frequency_l1 n (lt_of_lt_of_le (modulus_pos P hp0) hn) P hp0
    (primes_pairwise_coprime P hp)

#print axioms prefixCount_fiber
#print axioms signature_frequency_l1
#print axioms prefixCount_card_Icc
#print axioms signature_frequency_l1_primes
end
end Erdos883Second.Signature
