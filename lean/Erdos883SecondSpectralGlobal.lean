import Erdos883SecondSpectralOdd
import Erdos883SecondSixMean

/-! The full finite-signature stability theorem. All spectral projections,
three-signature couplings and the six-position means are derived here; no
arithmetic stability or triangle bound is assumed. The remaining arithmetic
bridge must bound this exact independent density by counted coprime triples. -/

namespace Erdos883.SecondSpectral

noncomputable section
open Erdos883Second.Far

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem blockTriangleMean_density_bound (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (t : Fin 7) :
    blockTriangleMean q f t ≤ 96 * Real.sqrt (fullTriangleDensity q f) := by
  let b2 : TripleBit := (sixParity (sixTriple t).1,
    sixParity (sixTriple t).2.1, sixParity (sixTriple t).2.2)
  let b3 : TripleBit := (sixThree (sixTriple t).1,
    sixThree (sixTriple t).2.1, sixThree (sixTriple t).2.2)
  have hb2 : tripleBitAllowed b2 := by
    fin_cases t <;> norm_num [b2, sixParity, sixTriple, tripleBitAllowed]
  have hb3 : tripleBitAllowed b3 := by
    fin_cases t <;> norm_num [b3, sixThree, sixTriple, tripleBitAllowed]
  rw [blockTriangleMean_tensor]
  change (∑ z : ι → TripleBit, tensorTripleWeight q z * fullTripleProduct f b2 b3 z) ≤ _
  apply tensorTriple_fixed_two_three_bound n q hqi hq hqn b2 b3 hb3
    (fullTripleProduct f b2 b3) (fullTripleProduct_bounds f hf b2 b3)
  exact fullTriangleDensity_fixed_slice q (fun i => (hq i).2) f
    (fun x => (hf x).1) b2 b3 hb2 hb3

 theorem fullEvenDeficit_density_bound (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (eps : ℝ)
    (hmean : 2 / 3 - eps ≤ fullSignatureMean q f) :
    1 - fullParityMean q f true ≤ 6 * eps + 1344 * Real.sqrt (fullTriangleDensity q f) := by
  have h := sixMean_even_deficit q hq f (fun x => (hf x).1) (fun x => (hf x).2)
    eps (96 * Real.sqrt (fullTriangleDensity q f)) hmean
    (blockTriangleMean_density_bound n q hqi hq hqn f hf)
  linarith

 theorem fullOddPair_density_bound (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (eps : ℝ)
    (hmean : 2 / 3 - eps ≤ fullSignatureMean q f) :
    fullOddPairCorrelation q f ≤ 6 * eps + 1392 * Real.sqrt (fullTriangleDensity q f) := by
  have heven := fullEvenDeficit_density_bound n q hqi hq hqn f hf eps hmean
  have hpair := fullOddPairCorrelation_bound n q hqi hq hqn f hf
  linarith

 theorem fullSignature_stability (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (eps : ℝ)
    (heps : 0 ≤ eps) (heps_small : eps ≤ 1 / 12)
    (hmean : 2 / 3 - eps ≤ fullSignatureMean q f)
    (hsmall : 7 * eps + 1392 * Real.sqrt (fullTriangleDensity q f) ≤ 1 / 48) :
    fullOutsideMass q f ≤ 8 * (7 * eps + 1392 * Real.sqrt (fullTriangleDensity q f)) := by
  have hpair := fullOddPair_density_bound n q hqi hq hqn f hf eps hmean
  have hsmall' : fullOddPairCorrelation q f + eps ≤ 1 / 48 := by linarith
  have hout := fullOutsideMass_spectral_small q hqi hq f hf eps heps heps_small hmean hsmall'
  linarith

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.blockTriangleMean_density_bound
#print axioms Erdos883.SecondSpectral.fullEvenDeficit_density_bound
#print axioms Erdos883.SecondSpectral.fullOddPair_density_bound
#print axioms Erdos883.SecondSpectral.fullSignature_stability
