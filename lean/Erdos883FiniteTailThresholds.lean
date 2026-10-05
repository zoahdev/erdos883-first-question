import Erdos883TailPowerBatch00
import Erdos883TailPowerBatch01
import Erdos883TailPowerBatch02
import Erdos883TailPowerBatch03
import Erdos883TailPowerBatch04
import Erdos883TailPowerBatch05
import Erdos883TailPowerBatch06
import Erdos883TailPowerBatch07
import Erdos883TailPowerBatch08
import Erdos883TailPowerBatch09
import Erdos883TailPowerBatch10
import Erdos883TailPowerBatch11
import Erdos883TailPowerBatch12
import Erdos883TailPowerBatch13
import Erdos883TailPowerBatch14
import Erdos883TailPowerBatch15
import Erdos883TailPowerBatch16
import Erdos883TailPowerBatch17
import Erdos883TailPowerBatch18
import Erdos883TailPowerBatch19
import Erdos883TailPowerBatch20
import Erdos883UniformTail
import Erdos883SmallTailCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

namespace Erdos883Verified

/-- An untrusted explicit coordinate witness; every numerical assertion below is kernel checked. -/
def finiteOddPrimeCoordinates : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671]

@[simp] theorem finiteOddPrimeCoordinates_length : finiteOddPrimeCoordinates.length = 511 := by decide

/-- Exact integer checks for the coarse Bernoulli estimate on all 502 middle scales. -/
theorem finiteTailThreshold_power_certificate :
    ∀ i : Fin 502,
      4 ^ (i.val + 9) <
        (finiteOddPrimeCoordinates[i.val + 9]'(by simp; omega)) ^
          ((finiteOddPrimeCoordinates[i.val + 9]'(by simp; omega) + 9) / 10) := by
  intro i
  have hc : finiteTailPowerPredicate i.val := by
    by_cases h0 : i.val < 24
    · have h := finiteTailPowerBatch00 ⟨i.val - 0, by omega⟩
      have heq : 0 + (i.val - 0) = i.val := by omega
      simpa only [heq] using h
    by_cases h1 : i.val < 48
    · have h := finiteTailPowerBatch01 ⟨i.val - 24, by omega⟩
      have heq : 24 + (i.val - 24) = i.val := by omega
      simpa only [heq] using h
    by_cases h2 : i.val < 72
    · have h := finiteTailPowerBatch02 ⟨i.val - 48, by omega⟩
      have heq : 48 + (i.val - 48) = i.val := by omega
      simpa only [heq] using h
    by_cases h3 : i.val < 96
    · have h := finiteTailPowerBatch03 ⟨i.val - 72, by omega⟩
      have heq : 72 + (i.val - 72) = i.val := by omega
      simpa only [heq] using h
    by_cases h4 : i.val < 120
    · have h := finiteTailPowerBatch04 ⟨i.val - 96, by omega⟩
      have heq : 96 + (i.val - 96) = i.val := by omega
      simpa only [heq] using h
    by_cases h5 : i.val < 144
    · have h := finiteTailPowerBatch05 ⟨i.val - 120, by omega⟩
      have heq : 120 + (i.val - 120) = i.val := by omega
      simpa only [heq] using h
    by_cases h6 : i.val < 168
    · have h := finiteTailPowerBatch06 ⟨i.val - 144, by omega⟩
      have heq : 144 + (i.val - 144) = i.val := by omega
      simpa only [heq] using h
    by_cases h7 : i.val < 192
    · have h := finiteTailPowerBatch07 ⟨i.val - 168, by omega⟩
      have heq : 168 + (i.val - 168) = i.val := by omega
      simpa only [heq] using h
    by_cases h8 : i.val < 216
    · have h := finiteTailPowerBatch08 ⟨i.val - 192, by omega⟩
      have heq : 192 + (i.val - 192) = i.val := by omega
      simpa only [heq] using h
    by_cases h9 : i.val < 240
    · have h := finiteTailPowerBatch09 ⟨i.val - 216, by omega⟩
      have heq : 216 + (i.val - 216) = i.val := by omega
      simpa only [heq] using h
    by_cases h10 : i.val < 264
    · have h := finiteTailPowerBatch10 ⟨i.val - 240, by omega⟩
      have heq : 240 + (i.val - 240) = i.val := by omega
      simpa only [heq] using h
    by_cases h11 : i.val < 288
    · have h := finiteTailPowerBatch11 ⟨i.val - 264, by omega⟩
      have heq : 264 + (i.val - 264) = i.val := by omega
      simpa only [heq] using h
    by_cases h12 : i.val < 312
    · have h := finiteTailPowerBatch12 ⟨i.val - 288, by omega⟩
      have heq : 288 + (i.val - 288) = i.val := by omega
      simpa only [heq] using h
    by_cases h13 : i.val < 336
    · have h := finiteTailPowerBatch13 ⟨i.val - 312, by omega⟩
      have heq : 312 + (i.val - 312) = i.val := by omega
      simpa only [heq] using h
    by_cases h14 : i.val < 360
    · have h := finiteTailPowerBatch14 ⟨i.val - 336, by omega⟩
      have heq : 336 + (i.val - 336) = i.val := by omega
      simpa only [heq] using h
    by_cases h15 : i.val < 384
    · have h := finiteTailPowerBatch15 ⟨i.val - 360, by omega⟩
      have heq : 360 + (i.val - 360) = i.val := by omega
      simpa only [heq] using h
    by_cases h16 : i.val < 408
    · have h := finiteTailPowerBatch16 ⟨i.val - 384, by omega⟩
      have heq : 384 + (i.val - 384) = i.val := by omega
      simpa only [heq] using h
    by_cases h17 : i.val < 432
    · have h := finiteTailPowerBatch17 ⟨i.val - 408, by omega⟩
      have heq : 408 + (i.val - 408) = i.val := by omega
      simpa only [heq] using h
    by_cases h18 : i.val < 456
    · have h := finiteTailPowerBatch18 ⟨i.val - 432, by omega⟩
      have heq : 432 + (i.val - 432) = i.val := by omega
      simpa only [heq] using h
    by_cases h19 : i.val < 480
    · have h := finiteTailPowerBatch19 ⟨i.val - 456, by omega⟩
      have heq : 456 + (i.val - 456) = i.val := by omega
      simpa only [heq] using h
    have h := finiteTailPowerBatch20 ⟨i.val - 480, by omega⟩
    have heq : 480 + (i.val - 480) = i.val := by omega
    simpa only [heq] using h
  unfold finiteTailPowerPredicate at hc
  have hdata : finiteTailPowerData = finiteOddPrimeCoordinates := rfl
  rw [hdata] at hc
  have hi : i.val + 9 < finiteOddPrimeCoordinates.length := by simp; omega
  simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hc


/-- A tiny exact proper-divisor test. Its success certifies compositeness. -/
def hasProperSmallDivisor (n : ℕ) : Bool :=
  (List.range 61).any (fun d => decide (1 < d ∧ d < n ∧ d ∣ n))

/-- Check the gaps between the candidate coordinates using proper divisors. -/
def primeCoordinateCoverCheck (stop lo : ℕ) : List ℕ → Bool
  | [] => (List.range (stop - lo)).all (fun i => hasProperSmallDivisor (lo + i))
  | p :: ps => (List.range (p - lo)).all (fun i => hasProperSmallDivisor (lo + i)) &&
      primeCoordinateCoverCheck stop (p + 1) ps

/-- A successful small-divisor test excludes primality. -/
theorem not_prime_of_hasProperSmallDivisor {n : ℕ}
    (h : hasProperSmallDivisor n = true) : ¬ n.Prime := by
  intro hn
  obtain ⟨d, _, hd⟩ := List.any_eq_true.mp h
  have hd' : 1 < d ∧ d < n ∧ d ∣ n := of_decide_eq_true hd
  rcases (Nat.dvd_prime hn).mp hd'.2.2 with hd | hd <;> omega

/-- Soundness of the gap certificate, independent of the supplied list. -/
theorem primeCoordinateCoverCheck_sound {stop lo q : ℕ} {ps : List ℕ}
    (h : primeCoordinateCoverCheck stop lo ps = true)
    (hq : q.Prime) (hlo : lo ≤ q) (hstop : q < stop) : q ∈ ps := by
  induction ps generalizing lo with
  | nil =>
    simp only [primeCoordinateCoverCheck, List.all_eq_true] at h
    have hi : q - lo ∈ List.range (stop - lo) := List.mem_range.mpr (by omega)
    have heq : lo + (q - lo) = q := by omega
    have hc := h (q - lo) hi
    rw [heq] at hc
    exact False.elim (not_prime_of_hasProperSmallDivisor hc hq)
  | cons p ps ih =>
    simp only [primeCoordinateCoverCheck, Bool.and_eq_true] at h
    by_cases hqp : q < p
    · have hi : q - lo ∈ List.range (p - lo) := List.mem_range.mpr (by omega)
      have heq : lo + (q - lo) = q := by omega
      have hc := List.all_eq_true.mp h.1 (q - lo) hi
      rw [heq] at hc
      exact False.elim (not_prime_of_hasProperSmallDivisor hc hq)
    · by_cases heq : q = p
      · simp [heq]
      · exact List.mem_cons_of_mem p (ih h.2 (by omega))

/-- One exact gap certificate covers every odd prime below 3672. -/
theorem finiteOddPrimeCoordinates_cover_certificate :
    primeCoordinateCoverCheck 3672 3 finiteOddPrimeCoordinates = true := by decide

/-- The coordinate witness is increasing. -/
theorem finiteOddPrimeCoordinates_sorted :
    finiteOddPrimeCoordinates.SortedLE := by decide

/-- Every witness entry lies below the certified coverage bound. -/
theorem finiteOddPrimeCoordinates_bound :
    ∀ q ∈ finiteOddPrimeCoordinates, 2 ≤ q ∧ q < 3672 := by decide

/-- Coverage of every odd prime up to the final threshold. -/
theorem finiteOddPrimeCoordinates_covers {q : ℕ}
    (hq : q.Prime) (hodd : Odd q) (hbound : q < 3672) :
    q ∈ finiteOddPrimeCoordinates := by
  apply primeCoordinateCoverCheck_sound finiteOddPrimeCoordinates_cover_certificate hq _ hbound
  have hq2 := hq.two_le
  have hmod := Nat.odd_iff.mp hodd
  omega

/-- A sorted complete witness gives complete coverage in every initial segment. -/
theorem sortedCoordinates_prefix_covers {ps : List ℕ} {q s : ℕ}
    (hs : s < ps.length) (hsorted : ps.SortedLE)
    (hmem : q ∈ ps) (hq : q < ps[s]) : q ∈ ps.take s := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  have his : i < s := by
    by_contra h
    have hle : ps[s] ≤ ps[i] := hsorted.getElem_le_getElem_of_le (by omega)
    omega
  exact List.mem_take_iff_getElem.mpr ⟨i, by omega, heq⟩

/-- Every initial segment includes all odd primes below its next entry. -/
theorem finiteOddPrimeCoordinates_prefix_covers {s q : ℕ}
    (hs : s < 511) (hq : q.Prime) (hodd : Odd q)
    (hqs : q < finiteOddPrimeCoordinates[s]'(by simp; omega)) :
    q ∈ finiteOddPrimeCoordinates.take s := by
  have hbound := finiteOddPrimeCoordinates_bound _ (List.getElem_mem (by simp; omega))
  exact sortedCoordinates_prefix_covers (by simp; omega)
    finiteOddPrimeCoordinates_sorted
    (finiteOddPrimeCoordinates_covers hq hodd (by omega)) hqs

/-- Kernel-checked finite power barriers imply the required cardinal inequality. -/
theorem ten_mul_lt_of_finiteTailThreshold {s a : ℕ} (hslo : 9 ≤ s) (hshi : s < 511)
    (hpow : (finiteOddPrimeCoordinates[s]'(by simp; omega)) ^ a ≤ 4 ^ s) :
    10 * a < finiteOddPrimeCoordinates[s]'(by simp; omega) := by
  let p := finiteOddPrimeCoordinates[s]'(by simp; omega)
  have hp := (finiteOddPrimeCoordinates_bound p (List.getElem_mem (by simp; omega))).1
  have hcheck := finiteTailThreshold_power_certificate ⟨s - 9, by omega⟩
  have hsub : s - 9 + 9 = s := by omega
  simp only [hsub] at hcheck
  by_contra h
  have ha : (p + 9) / 10 ≤ a := by omega
  have hle : p ^ ((p + 9) / 10) ≤ p ^ a := pow_le_pow_right' (by omega) ha
  dsimp [p] at hle
  omega

/-- Uniform nine-tenths preservation for all 502 middle scales. -/
theorem totientDensity_lcm_gt_nine_tenths_of_finiteTailThreshold
    {u v s : ℕ} (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v)
    (hslo : 9 ≤ s) (hshi : s < 511) (hvU : v ≤ 4 ^ s)
    (hcode : divisorSignatureCode (finiteOddPrimeCoordinates.take s) u =
      divisorSignatureCode (finiteOddPrimeCoordinates.take s) v) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  let p := finiteOddPrimeCoordinates[s]'(by simp; omega)
  have hp := (finiteOddPrimeCoordinates_bound p (List.getElem_mem (by simp; omega))).1
  have hsmall := missingPrime_ge_of_odd_signature_eq hu hvodd
    (fun q hq ho hqp => finiteOddPrimeCoordinates_prefix_covers hshi hq ho hqp) hcode
  have hpow := primeFactors_subset_pow_card_le hv hvU Finset.sdiff_subset hsmall
  have hcard := ten_mul_lt_of_finiteTailThreshold hslo hshi hpow
  have hfac := thresholdFactor_pow_gt_nine_tenths hp hcard
  have htail := totientDensity_lcm_ge_tailFactor hu hv hp hsmall
    (show (v.primeFactors \ u.primeFactors).card ≤
      (v.primeFactors \ u.primeFactors).card from le_rfl)
  exact lt_of_lt_of_le
    (by simpa [mul_comm] using mul_lt_mul_of_pos_left hfac (totientDensity_pos hu)) htail


/-- The three initial scales, using the exact distinct-prime bounds. -/
theorem totientDensity_lcm_gt_nine_tenths_of_smallTailThreshold
    {u v s : ℕ} (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v)
    (hslo : 6 ≤ s) (hshi : s < 9) (hvU : v ≤ 4 ^ s)
    (hcode : divisorSignatureCode (finiteOddPrimeCoordinates.take s) u =
      divisorSignatureCode (finiteOddPrimeCoordinates.take s) v) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  let S := v.primeFactors \ u.primeFactors
  have hsmall := missingPrime_ge_of_odd_signature_eq
    (p := finiteOddPrimeCoordinates[s]'(by simp; omega)) hu hvodd
    (fun q hq ho hqp => finiteOddPrimeCoordinates_prefix_covers (s := s) (by omega) hq ho hqp) hcode
  have hprime : ∀ q ∈ S, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
  have hprod : (∏ q ∈ S, q) ≤ 4 ^ s :=
    (Nat.le_of_dvd hv (prod_primeFactors_subset_dvd Finset.sdiff_subset)).trans hvU
  have hfac : (9 / 10 : ℚ) < ∏ q ∈ S, (1 - (q : ℚ)⁻¹) := by
    have hcases : s = 6 ∨ s = 7 ∨ s = 8 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact primeFinset_tailFactor_gt_nine_tenths_scale_six hprime hsmall hprod
    · exact primeFinset_tailFactor_gt_nine_tenths_scale_seven hprime hsmall hprod
    · exact primeFinset_tailFactor_gt_nine_tenths_scale_eight hsmall hprod
  rw [totientDensity_lcm_eq_mul_prod_sdiff hu hv]
  simpa only [S, mul_comm] using mul_lt_mul_of_pos_left hfac (totientDensity_pos hu)

/-- Every one of the 505 finite scales has the same nine-tenths tail guarantee. -/
theorem totientDensity_lcm_gt_nine_tenths_of_finite_prefix
    {u v s : ℕ} (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v)
    (hslo : 6 ≤ s) (hshi : s < 511) (hvU : v ≤ 4 ^ s)
    (hcode : divisorSignatureCode (finiteOddPrimeCoordinates.take s) u =
      divisorSignatureCode (finiteOddPrimeCoordinates.take s) v) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  by_cases hs9 : 9 ≤ s
  · exact totientDensity_lcm_gt_nine_tenths_of_finiteTailThreshold
      hu hv hvodd hs9 hshi hvU hcode
  · exact totientDensity_lcm_gt_nine_tenths_of_smallTailThreshold
      hu hv hvodd hslo (by omega) hvU hcode

/-- A coherent coordinate family: the 511 checked coordinates, then all
 remaining odd integers. Every prefix is again a member of this family. -/
def adaptiveTailCoordinates (r : ℕ) : List ℕ :=
  finiteOddPrimeCoordinates.take r ++
    (List.range (r - 511)).map (fun i => 3673 + 2 * i)

@[simp] theorem adaptiveTailCoordinates_length (r : ℕ) :
    (adaptiveTailCoordinates r).length = r := by
  simp only [adaptiveTailCoordinates, List.length_append, List.length_take,
    finiteOddPrimeCoordinates_length, List.length_map, List.length_range]
  omega

/-- At finite scales the adaptive coordinates are the checked witness prefix. -/
theorem adaptiveTailCoordinates_eq_finite {r : ℕ} (hr : r ≤ 511) :
    adaptiveTailCoordinates r = finiteOddPrimeCoordinates.take r := by
  simp [adaptiveTailCoordinates, Nat.sub_eq_zero_of_le hr]

/-- Taking an initial segment commutes with the adaptive coordinate construction. -/
theorem adaptiveTailCoordinates_take {r s : ℕ} (hsr : s ≤ r) :
    (adaptiveTailCoordinates r).take s = adaptiveTailCoordinates s := by
  simp only [adaptiveTailCoordinates, List.take_append, List.take_take,
    List.length_take, finiteOddPrimeCoordinates_length, ← List.map_take, List.take_range]
  have hmin : min s r = s := Nat.min_eq_left hsr
  rw [hmin]
  have hmin' : min (s - min r 511) (r - 511) = s - 511 := by omega
  rw [hmin']

/-- For every large scale, the adaptive coordinates cover all odd primes
 below a threshold at least `2s+3`. -/
theorem adaptiveTailCoordinates_covers_large {s q : ℕ}
    (hs : 511 ≤ s) (hq : q.Prime) (hodd : Odd q) (hqs : q < 2 * s + 2651) :
    q ∈ adaptiveTailCoordinates s := by
  have htake : finiteOddPrimeCoordinates.take s = finiteOddPrimeCoordinates :=
    List.take_of_length_le (by simpa using hs)
  simp only [adaptiveTailCoordinates, htake, List.mem_append]
  by_cases hq3672 : q < 3672
  · exact Or.inl (finiteOddPrimeCoordinates_covers hq hodd hq3672)
  · apply Or.inr
    have hmod := Nat.odd_iff.mp hodd
    have hdiv := Nat.mod_add_div q 2
    apply List.mem_map.mpr
    refine ⟨q / 2 - 1836, List.mem_range.mpr (by omega), ?_⟩
    omega

/-- The uniform adaptive nine-tenths bound at every scale at least six. -/
theorem totientDensity_lcm_gt_nine_tenths_of_adaptive_signature
    {u v s : ℕ} (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v)
    (hs : 6 ≤ s) (hvU : v ≤ 4 ^ s)
    (hcode : divisorSignatureCode (adaptiveTailCoordinates s) u =
      divisorSignatureCode (adaptiveTailCoordinates s) v) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  by_cases hlarge : 511 ≤ s
  · exact totientDensity_lcm_gt_nine_tenths_of_large_signature hu hv hvodd hlarge
      (show 2 * s + 3 ≤ 2 * s + 2651 by omega) hvU
      (fun q hq ho hqp => adaptiveTailCoordinates_covers_large hlarge hq ho hqp) hcode
  · rw [adaptiveTailCoordinates_eq_finite (by omega)] at hcode
    exact totientDensity_lcm_gt_nine_tenths_of_finite_prefix hu hv hvodd hs (by omega) hvU hcode

/-- One full coordinate order supports the uniform bound at all its prefixes. -/
theorem totientDensity_lcm_gt_nine_tenths_of_adaptive_prefix
    {u v r s : ℕ} (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v)
    (hs : 6 ≤ s) (hsr : s ≤ r) (hvU : v ≤ 4 ^ s)
    (hcode : divisorSignatureCode (adaptiveTailCoordinates r) u / 2 ^ (r - s) =
      divisorSignatureCode (adaptiveTailCoordinates r) v / 2 ^ (r - s)) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  apply totientDensity_lcm_gt_nine_tenths_of_adaptive_signature hu hv hvodd hs hvU
  have hc : divisorSignatureCode ((adaptiveTailCoordinates r).take s) u =
      divisorSignatureCode ((adaptiveTailCoordinates r).take s) v := by
    simpa only [← divisorSignatureCode_take, adaptiveTailCoordinates_length] using hcode
  simpa only [adaptiveTailCoordinates_take hsr] using hc

/-- The least integral scale with `U ≤ 4^s`. -/
def uniformTailScale (U : ℕ) : ℕ := Nat.clog 4 U

/-- The chosen scale is indeed an upper scale. -/
theorem le_four_pow_uniformTailScale (U : ℕ) : U ≤ 4 ^ uniformTailScale U :=
  Nat.le_pow_clog (by decide) U

/-- Minimality of the chosen scale. -/
theorem uniformTailScale_minimal {U s : ℕ} (h : U ≤ 4 ^ s) : uniformTailScale U ≤ s :=
  Nat.clog_le_of_le_pow h

/-- Every size beyond 1024 lies in the verified adaptive range. -/
theorem uniformTailScale_ge_six {U : ℕ} (hU : 1024 < U) : 6 ≤ uniformTailScale U := by
  have h : 5 < Nat.clog 4 U := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simpa using hU)
  exact h

/-- Uniform tail preservation for every ambient size above 1024, using its
 least power-of-four scale and exactly that many signature coordinates. -/
theorem totientDensity_lcm_gt_nine_tenths_uniform
    {U u v : ℕ} (hU : 1024 < U) (hu : 0 < u) (hv : 0 < v)
    (hvodd : Odd v) (hvU : v ≤ U)
    (hcode : divisorSignatureCode (adaptiveTailCoordinates (uniformTailScale U)) u =
      divisorSignatureCode (adaptiveTailCoordinates (uniformTailScale U)) v) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  exact totientDensity_lcm_gt_nine_tenths_of_adaptive_signature hu hv hvodd
    (uniformTailScale_ge_six hU) (hvU.trans (le_four_pow_uniformTailScale U)) hcode


/-- The first five profile coordinates are the usual first five odd primes. -/
theorem adaptiveTailCoordinates_take_five {r : ℕ} (hr : 5 ≤ r) :
    (adaptiveTailCoordinates r).take 5 = [3, 5, 7, 11, 13] := by
  rw [adaptiveTailCoordinates_take hr]
  rfl

/-- The previous scale is strictly below `U`, as required by minimality. -/
theorem four_pow_pred_uniformTailScale_lt {U : ℕ} (hU : 1024 < U) :
    4 ^ (uniformTailScale U - 1) < U := by
  have hs := uniformTailScale_ge_six hU
  exact Nat.pow_lt_of_lt_clog (show uniformTailScale U - 1 < Nat.clog 4 U by
    change uniformTailScale U - 1 < uniformTailScale U
    omega)

end Erdos883Verified
#print axioms Erdos883Verified.finiteOddPrimeCoordinates_length
#print axioms Erdos883Verified.finiteTailThreshold_power_certificate

#print axioms Erdos883Verified.not_prime_of_hasProperSmallDivisor
#print axioms Erdos883Verified.primeCoordinateCoverCheck_sound
#print axioms Erdos883Verified.finiteOddPrimeCoordinates_cover_certificate
#print axioms Erdos883Verified.finiteOddPrimeCoordinates_sorted
#print axioms Erdos883Verified.finiteOddPrimeCoordinates_bound
#print axioms Erdos883Verified.finiteOddPrimeCoordinates_covers
#print axioms Erdos883Verified.sortedCoordinates_prefix_covers
#print axioms Erdos883Verified.finiteOddPrimeCoordinates_prefix_covers
#print axioms Erdos883Verified.ten_mul_lt_of_finiteTailThreshold
#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_of_finiteTailThreshold

#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_of_smallTailThreshold
#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_of_finite_prefix
#print axioms Erdos883Verified.adaptiveTailCoordinates_length
#print axioms Erdos883Verified.adaptiveTailCoordinates_eq_finite
#print axioms Erdos883Verified.adaptiveTailCoordinates_take
#print axioms Erdos883Verified.adaptiveTailCoordinates_covers_large
#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_of_adaptive_signature
#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_of_adaptive_prefix
#print axioms Erdos883Verified.le_four_pow_uniformTailScale
#print axioms Erdos883Verified.uniformTailScale_minimal
#print axioms Erdos883Verified.uniformTailScale_ge_six
#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_uniform

#print axioms Erdos883Verified.adaptiveTailCoordinates_take_five
#print axioms Erdos883Verified.four_pow_pred_uniformTailScale_lt
