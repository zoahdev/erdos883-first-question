import Erdos883SecondSpectralConditional
import Mathlib.Data.Fintype.Option

namespace Erdos883.SecondSpectral

noncomputable section

variable (ι : Type*)

abbrev FullSignature := Bool × Bool × (ι → Bool)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullSignatureWeight (q : ι → ℕ) (x : FullSignature ι) : ℝ :=
  coordinateWeight 2 x.1 * coordinateWeight 3 x.2.1 *
    tensorWeight (fun i => (q i : ℝ)) x.2.2

def fullSignatureMean (q : ι → ℕ) (f : FullSignature ι → ℝ) : ℝ :=
  ∑ x : FullSignature ι, fullSignatureWeight q x * f x

def fullParityMean (q : ι → ℕ) (f : FullSignature ι → ℝ) (b : Bool) : ℝ :=
  ∑ t : Bool × (ι → Bool), coordinateWeight 3 t.1 *
    tensorWeight (fun i => (q i : ℝ)) t.2 * f (b, t.1, t.2)

def fullOutsideMass (q : ι → ℕ) (f : FullSignature ι → ℝ) : ℝ :=
  ∑ x : FullSignature ι, fullSignatureWeight q x * f x *
    (if x.1 = false ∧ x.2.1 = false then 1 else 0)

def oddPrimeLabels (q : ι → ℕ) : Option ι → ℕ
  | none => 3
  | some i => q i

def splitThreeBits : (Option ι → Bool) ≃ Bool × (ι → Bool) where
  toFun x := (x none, fun i => x (some i))
  invFun x := fun i => match i with | none => x.1 | some j => x.2 j
  left_inv x := by funext i; cases i <;> rfl
  right_inv x := by rcases x with ⟨b, y⟩; rfl

def fullParityFunction (f : FullSignature ι → ℝ) (b : Bool)
    (x : Option ι → Bool) : ℝ := f (b, x none, fun i => x (some i))

def fullOddPairCorrelation (q : ι → ℕ) (f : FullSignature ι → ℝ) : ℝ :=
  tensorPairCorrelation (fun i => (oddPrimeLabels q i : ℝ))
    (fullParityFunction f false) (fullParityFunction f false)

 theorem fullSignatureMean_parity (q : ι → ℕ) (f : FullSignature ι → ℝ) :
    fullSignatureMean q f =
      (fullParityMean q f false + fullParityMean q f true) / 2 := by
  have h : fullSignatureMean q f =
      ∑ b : Bool, coordinateWeight 2 b * fullParityMean q f b := by
    simp only [fullSignatureMean, fullSignatureWeight, fullParityMean,
      Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h]
  simp [Fintype.univ_bool, coordinateWeight]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem oddPrimeLabels_injective (q : ι → ℕ) (hqi : Function.Injective q)
    (hq : ∀ i, 5 ≤ q i) : Function.Injective (oddPrimeLabels q) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => have h := hq j; simp only [oddPrimeLabels] at hab; omega
  | some i =>
    cases b with
    | none => have h := hq i; simp only [oddPrimeLabels] at hab; omega
    | some j => exact congrArg some (hqi hab)

omit [Fintype ι] [DecidableEq ι] in
theorem oddPrimeLabels_prime (q : ι → ℕ) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i) :
    ∀ i, (oddPrimeLabels q i).Prime ∧ 3 ≤ oddPrimeLabels q i := by
  intro i
  cases i with
  | none => exact ⟨Nat.prime_three, by change 3 ≤ 3; omega⟩
  | some i => exact ⟨(hq i).1, Nat.le_trans (by norm_num) (hq i).2⟩

omit [DecidableEq ι] in
theorem tensorWeight_withThree (q : ι → ℕ) (x : Option ι → Bool) :
    tensorWeight (fun i => (oddPrimeLabels q i : ℝ)) x =
      coordinateWeight 3 (x none) * tensorWeight (fun i => (q i : ℝ))
        (fun i => x (some i)) := by
  simp only [tensorWeight, Fintype.prod_option, oddPrimeLabels, Nat.cast_ofNat]

 theorem fullParityMean_tensorMean (q : ι → ℕ) (f : FullSignature ι → ℝ) (b : Bool) :
    tensorMean (fun i => (oddPrimeLabels q i : ℝ)) (fullParityFunction f b) =
      fullParityMean q f b := by
  unfold tensorMean fullParityMean
  apply Fintype.sum_equiv splitThreeBits
  intro x
  rw [tensorWeight_withThree]
  rfl

 theorem fullOutsideMass_tensorSlice (q : ι → ℕ) (f : FullSignature ι → ℝ) :
    fullOutsideMass q f =
      tensorSliceMass (fun i => (oddPrimeLabels q i : ℝ))
        (fullParityFunction f false) none false / 2 := by
  have hslice : tensorSliceMass (fun i => (oddPrimeLabels q i : ℝ))
        (fullParityFunction f false) none false =
      ∑ t : Bool × (ι → Bool), coordinateWeight 3 t.1 *
        tensorWeight (fun i => (q i : ℝ)) t.2 * f (false, t.1, t.2) *
          (if t.1 = false then 1 else 0) := by
    unfold tensorSliceMass
    apply Fintype.sum_equiv splitThreeBits
    intro x
    rw [tensorWeight_withThree]
    rfl
  rw [hslice]
  simp only [fullOutsideMass, fullSignatureWeight, Fintype.sum_prod_type]
  simp [Fintype.univ_bool, coordinateWeight]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

 theorem fullParityMean_bounds (q : ι → ℕ) (hq : ∀ i, 5 ≤ q i)
    (f : FullSignature ι → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (b : Bool) :
    0 ≤ fullParityMean q f b ∧ fullParityMean q f b ≤ 1 := by
  let p : Option ι → ℝ := fun i => (oddPrimeLabels q i : ℝ)
  have hp : ∀ i, 1 ≤ p i := by
    intro i
    cases i with
    | none => norm_num [p, oddPrimeLabels]
    | some i => have hh : (5 : ℝ) ≤ q i := by exact_mod_cast hq i
                dsimp [p, oddPrimeLabels]; linarith
  have hp0 : ∀ i, p i ≠ 0 := by intro i; linarith [hp i]
  rw [← fullParityMean_tensorMean]
  constructor
  · apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (tensorWeight_nonneg p hp x) (hf _).1
  · have hle : tensorMean p (fullParityFunction f b) ≤
        ∑ x : Option ι → Bool, tensorWeight p x := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_of_le_one_right (tensorWeight_nonneg p hp x) (hf _).2
    rw [tensorWeight_sum p hp0] at hle
    exact hle

/-- Quantitative stability in the full finite signature model, with the
precise density threshold 2/3 minus the finite counting error eps. -/
 theorem fullOutsideMass_spectral_small (q : ι → ℕ) (hqi : Function.Injective q)
    (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i) (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (eps : ℝ) (heps : 0 ≤ eps)
    (heps_small : eps ≤ 1 / 12) (hmean : 2 / 3 - eps ≤ fullSignatureMean q f)
    (hsmall : fullOddPairCorrelation q f + eps ≤ 1 / 48) :
    fullOutsideMass q f ≤ 8 * (fullOddPairCorrelation q f + eps) := by
  have heven := (fullParityMean_bounds q (fun i => (hq i).2) f hf true).2
  have hmeanpart := fullSignatureMean_parity q f
  have hmu : 1 / 3 - 2 * eps ≤ fullParityMean q f false := by linarith
  rw [fullOutsideMass_tensorSlice]
  apply tensorOutsideMass_small (oddPrimeLabels q)
    (oddPrimeLabels_injective q hqi (fun i => (hq i).2))
    (oddPrimeLabels_prime q hq) none rfl (fullParityFunction f false)
    (fun x => hf _) eps heps heps_small
  · rwa [fullParityMean_tensorMean]
  · exact hsmall

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.fullOutsideMass_spectral_small

