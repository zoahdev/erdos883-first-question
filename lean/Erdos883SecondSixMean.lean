import Erdos883SecondSixTensor
import Erdos883SecondSixFractional
import Erdos883SecondSpectralFull

namespace Erdos883Second.Far

open scoped BigOperators
open Erdos883.SecondSpectral
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sixParity (i : Fin 6) : Bool := decide (i.val = 1 ∨ i.val = 3 ∨ i.val = 5)
def sixThree (i : Fin 6) : Bool := decide (i.val = 2 ∨ i.val = 5)

def sixFullSignature (q : ι → ℕ) (x : ι → Fin 7) (i : Fin 6) : FullSignature ι :=
  (sixParity i, sixThree i, sixSignatureAt q x i)

def fullSliceMean (q : ι → ℕ) (f : FullSignature ι → ℝ) (b2 b3 : Bool) : ℝ :=
  ∑ z : ι → Bool, tensorWeight (fun i => (q i : ℝ)) z * f (b2, b3, z)

def blockTriangleMean (q : ι → ℕ) (f : FullSignature ι → ℝ) (t : Fin 7) : ℝ :=
  ∑ x : ι → Fin 7, sixTensorMass q x *
    (f (sixFullSignature q x (sixTriple t).1) *
     f (sixFullSignature q x (sixTriple t).2.1) *
     f (sixFullSignature q x (sixTriple t).2.2))

theorem fullParityMean_slices (q : ι → ℕ) (f : FullSignature ι → ℝ) (b : Bool) :
    fullParityMean q f b = (2 / 3) * fullSliceMean q f b false +
      (1 / 3) * fullSliceMean q f b true := by
  simp only [fullParityMean, Fintype.sum_prod_type]
  norm_num [Fintype.univ_bool, coordinateWeight, fullSliceMean, Finset.mul_sum, mul_assoc]
  ring

theorem sixFullSignature_mean (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (f : FullSignature ι → ℝ) (i : Fin 6) :
    (∑ x : ι → Fin 7, sixTensorMass q x * f (sixFullSignature q x i)) =
      fullSliceMean q f (sixParity i) (sixThree i) :=
  sixTensor_signature_expectation q hq i (fun z => f (sixParity i, sixThree i, z))

theorem blockTriangleMean_tensor (q : ι → ℕ) (f : FullSignature ι → ℝ) (t : Fin 7) :
    blockTriangleMean q f t =
      ∑ z : ι → TripleBit, tensorTripleWeight q z *
        (f (sixParity (sixTriple t).1, sixThree (sixTriple t).1, fun i => (z i).1) *
         f (sixParity (sixTriple t).2.1, sixThree (sixTriple t).2.1, fun i => (z i).2.1) *
         f (sixParity (sixTriple t).2.2, sixThree (sixTriple t).2.2, fun i => (z i).2.2)) :=
  sixTensor_triangle_expectation q t (fun z =>
    f (sixParity (sixTriple t).1, sixThree (sixTriple t).1, fun i => (z i).1) *
    f (sixParity (sixTriple t).2.1, sixThree (sixTriple t).2.1, fun i => (z i).2.1) *
    f (sixParity (sixTriple t).2.2, sixThree (sixTriple t).2.2, fun i => (z i).2.2))

theorem sixMean_even_deficit (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (f : FullSignature ι → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hf1 : ∀ s, f s ≤ 1)
    (eps c : ℝ) (hmean : 2 / 3 - eps ≤ fullSignatureMean q f)
    (htri : ∀ t : Fin 7, blockTriangleMean q f t ≤ c) :
    1 - fullParityMean q f true ≤ 6 * eps + 14 * c := by
  let r : (ι → Fin 7) → Fin 6 → ℝ := fun x i => f (sixFullSignature q x i)
  have hq0 : ∀ i, q i ≠ 0 := fun i => (hq i).1.ne_zero
  have hsmean (i : Fin 6) : (∑ x, sixTensorMass q x * r x i) =
      fullSliceMean q f (sixParity i) (sixThree i) :=
    sixFullSignature_mean q hq0 f i
  have heven : (∑ x, sixTensorMass q x * (r x 1 + r x 3 + r x 5)) =
      3 * fullParityMean q f true := by
    simp only [mul_add, Finset.sum_add_distrib, hsmean]
    rw [fullParityMean_slices]
    norm_num [sixParity, sixThree]
    ring
  have hall : (∑ x, sixTensorMass q x *
      (r x 0 + r x 1 + r x 2 + r x 3 + r x 4 + r x 5)) =
      6 * fullSignatureMean q f := by
    simp only [mul_add, Finset.sum_add_distrib, hsmean]
    rw [fullSignatureMean_parity, fullParityMean_slices, fullParityMean_slices]
    norm_num [sixParity, sixThree]
    ring
  have htri_sum : (∑ x, sixTensorMass q x * sixTriangleProducts (r x)) ≤ 7 * c := by
    have heq : (∑ x, sixTensorMass q x * sixTriangleProducts (r x)) =
        ∑ t : Fin 7, blockTriangleMean q f t := by
      simp [sixTriangleProducts, mul_add, Finset.sum_add_distrib,
        Fin.sum_univ_succ, blockTriangleMean, sixTriple, r] <;> ring
    rw [heq]
    calc
      _ ≤ ∑ _t : Fin 7, c := Finset.sum_le_sum (fun t _ => htri t)
      _ = _ := by simp
  have hp : (∑ x, sixTensorMass q x * (3 - (r x 1 + r x 3 + r x 5))) ≤
      ∑ x, sixTensorMass q x *
        (3 * (4 - (r x 0 + r x 1 + r x 2 + r x 3 + r x 4 + r x 5)) +
         6 * sixTriangleProducts (r x)) := by
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (six_fractional_pointwise (r x)
      (fun _ => hf0 _) (fun _ => hf1 _)) (sixTensorMass_nonneg q hq x)
  have hleft : (∑ x, sixTensorMass q x * (3 - (r x 1 + r x 3 + r x 5))) =
      3 - 3 * fullParityMean q f true := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [sixTensorMass_sum, heven]
    ring
  have hright : (∑ x, sixTensorMass q x *
        (3 * (4 - (r x 0 + r x 1 + r x 2 + r x 3 + r x 4 + r x 5)) +
         6 * sixTriangleProducts (r x))) =
      12 - 18 * fullSignatureMean q f +
        6 * (∑ x, sixTensorMass q x * sixTriangleProducts (r x)) := by
    have heq (x : ι → Fin 7) : sixTensorMass q x *
        (3 * (4 - (r x 0 + r x 1 + r x 2 + r x 3 + r x 4 + r x 5)) +
         6 * sixTriangleProducts (r x)) =
        sixTensorMass q x * 12 - 3 * (sixTensorMass q x *
          (r x 0 + r x 1 + r x 2 + r x 3 + r x 4 + r x 5)) +
          6 * (sixTensorMass q x * sixTriangleProducts (r x)) := by ring
    simp_rw [heq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, sixTensorMass_sum, ← Finset.mul_sum, hall, ← Finset.mul_sum]
    ring
  rw [hleft, hright] at hp
  linarith

#print axioms blockTriangleMean_tensor
#print axioms sixMean_even_deficit

end
end Erdos883Second.Far
