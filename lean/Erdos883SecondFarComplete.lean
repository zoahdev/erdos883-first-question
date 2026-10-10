import Erdos883SecondAssembly
import Erdos883SecondFarBudgets
import Erdos883SecondSignatureBounds
import Erdos883SecondSignatureTriangles
import Erdos883SecondSpectralGlobal

/-! The far branch with the cutoff and all thresholds fixed before the
integer set is chosen. Together with NearComplete this proves the exact
second-question statement, without a conditional stability premise. -/

namespace Erdos883Second
noncomputable section
open Signature
open Erdos883.SecondSpectral

theorem farBranch : FarBranch := by
  intro l hl delta hd
  have hdR : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hd
  let s : ℝ := min ((delta : ℝ) / 32) (1 / 1000)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hsdelta : s ≤ (delta : ℝ) / 32 := min_le_left _ _
  have hs1000 : s ≤ (1 : ℝ) / 1000 := min_le_right _ _
  let g : ℝ := (s / 2784)^2
  have hg : 0 < g := by dsimp [g]; positivity
  obtain ⟨K, hK, Ntri, htri⟩ := Link.smallPrimeTriangleDensity_eventually_small l hl
    (show 0 < g / 2 by positivity)
  let P := cutoffPrimes K
  have hp : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact ((mem_cutoffPrimes K p).mp hp).1
  have hp0 : ∀ p ∈ P, 0 < p := fun p h => (hp p h).pos
  have hc : Set.Pairwise (P : Set ℕ) Nat.Coprime := primes_pairwise_coprime P hp
  have h2 : 2 ∈ P := (mem_cutoffPrimes K 2).mpr ⟨Nat.prime_two, by omega⟩
  have h3 : 3 ∈ P := (mem_cutoffPrimes K 3).mpr ⟨Nat.prime_three, by omega⟩
  obtain ⟨Nbudget, hbudget⟩ := Far.counting_budgets_eventually (modulus P) s g delta
    hs hg hdR
  refine ⟨max Ntri Nbudget, ?_⟩
  intro n hn A hA hcard hfar
  by_contra hno
  obtain ⟨hn0, heps, hDerror, houtError⟩ :=
    hbudget n ((Nat.le_max_right _ _).trans hn)
  have hactual := htri n ((Nat.le_max_left _ _).trans hn) A hA hno
  let f := fullOccupancy n P h2 h3 A
  let eps : ℝ := (2 + (modulus P : ℝ)) / n
  have hD : fullTriangleDensity (bigPrimeValue P) f ≤ g := by
    have hh := full_triangle_density_le_actual n K hn0 h2 h3 A hA
    change fullTriangleDensity (bigPrimeValue P) f ≤ _ at hh
    linarith
  have hmean : 2 / 3 - eps ≤ fullSignatureMean (bigPrimeValue P) f :=
    full_occupancy_mean_lower_of_dense n hn0 P hp0 hc h2 h3 A hA hcard
  have heps0 : 0 ≤ eps := by dsimp [eps]; positivity
  have heps12 : eps ≤ 1 / 12 := by
    change eps ≤ s / 14 at heps
    linarith
  have htotal : 7 * eps + 1392 * Real.sqrt (fullTriangleDensity (bigPrimeValue P) f) ≤ s :=
    Far.signature_error_budget hs heps hD
  have hsmall : 7 * eps + 1392 * Real.sqrt (fullTriangleDensity (bigPrimeValue P) f) ≤ 1 / 48 :=
    htotal.trans (by linarith)
  have hqi := bigPrimeValue_injective P
  have hq : ∀ i, (bigPrimeValue P i).Prime ∧ 5 ≤ bigPrimeValue P i :=
    fun i => ⟨bigPrimeValue_prime P hp i, bigPrimeValue_ge_five P hp i⟩
  have hqK : ∀ i, bigPrimeValue P i ≤ K := by
    intro i
    exact ((mem_cutoffPrimes K i).mp (bigPrimes_subset P i.property)).2
  have hout := fullSignature_stability K (bigPrimeValue P) hqi hq hqK f
    (fullOccupancy_bounds n P h2 h3 A hA) eps heps0 heps12 hmean hsmall
  have hfarR : (delta : ℝ) * n ≤ ((A \ Near.standardUniverse n).card : ℝ) := by
    exact_mod_cast hfar
  have hlower := full_occupancy_outside_lower_of_far n hn0 P hp0 hc h2 h3 A hA delta hfarR
  change (delta : ℝ) ≤ fullOutsideMass (bigPrimeValue P) f + (modulus P : ℝ) / n at hlower
  linarith

theorem secondQuestion : SecondQuestion := secondQuestion_of_farBranch farBranch

#print axioms farBranch
#print axioms secondQuestion
end
end Erdos883Second
