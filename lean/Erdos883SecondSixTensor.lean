import Erdos883SecondSixCoordinate
import Erdos883SecondTensorPushforward
import Erdos883SecondSpectralTriple

namespace Erdos883Second.Far

open scoped BigOperators
open Erdos883.SecondSpectral
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sixTensorMass (p : ι → ℕ) (x : ι → Fin 7) : ℝ :=
  productMass (fun j r => (sixRootMass (p j) r : ℝ)) x

def sixSignatureAt (p : ι → ℕ) (x : ι → Fin 7) (i : Fin 6) : ι → Bool :=
  fun j => sixRootBit (p j) (x j) i

def sixTripleAt (p : ι → ℕ) (x : ι → Fin 7) (t : Fin 7) :
    ι → Bool × Bool × Bool := fun j => sixRootTriple (p j) t (x j)

theorem sixTensorMass_sum (p : ι → ℕ) :
    (∑ x : ι → Fin 7, sixTensorMass p x) = 1 := by
  apply productMass_sum
  intro i
  exact_mod_cast sixRootMass_sum (p i)

theorem sixTensorMass_nonneg (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (x : ι → Fin 7) :
    0 ≤ sixTensorMass p x := by
  apply Finset.prod_nonneg
  intro i _
  change 0 ≤ (sixRootMass (p i) (x i) : ℝ)
  exact_mod_cast sixRootMass_nonneg (hp i).1 (hp i).2 (x i)

theorem sixRootBit_real_fiber (p : ℕ) (hp : p ≠ 0) (i : Fin 6) (b : Bool) :
    fiberMass (fun r => (sixRootMass p r : ℝ)) (fun r => sixRootBit p r i) b =
      coordinateWeight (p : ℝ) b := by
  have h : fiberMass (fun r => (sixRootMass p r : ℝ)) (fun r => sixRootBit p r i) b =
      (bernoulliMass (1 / p) b : ℝ) := by
    unfold fiberMass
    dsimp only
    have h := congrArg (fun a : ℚ => (a : ℝ)) (sixRootBit_marginal p i b)
    simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using h
  rw [h]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  cases b <;> simp [bernoulliMass, coordinateWeight]
  field_simp

theorem sixRootTriple_real_fiber (p : ℕ) (t : Fin 7) (z : Bool × Bool × Bool) :
    fiberMass (fun r => (sixRootMass p r : ℝ)) (fun r => sixRootTriple p t r) z =
      coordinateTripleWeight p z := by
  unfold fiberMass coordinateTripleWeight
  dsimp only
  have h := congrArg (fun a : ℚ => (a : ℝ)) (sixRootTriple_marginal p t z)
  simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using h

theorem sixTensor_signature_expectation (p : ι → ℕ) (hp : ∀ j, p j ≠ 0)
    (i : Fin 6) (F : (ι → Bool) → ℝ) :
    (∑ x : ι → Fin 7, sixTensorMass p x * F (sixSignatureAt p x i)) =
      ∑ z : ι → Bool, tensorWeight (fun j => (p j : ℝ)) z * F z := by
  have h := product_expectation_pushforward
    (fun j r => (sixRootMass (p j) r : ℝ)) (fun j r => sixRootBit (p j) r i) F
  dsimp only [productMass] at h
  simp_rw [sixRootBit_real_fiber _ (hp _) i] at h
  exact h

theorem sixTensor_triangle_expectation (p : ι → ℕ) (t : Fin 7)
    (F : (ι → Bool × Bool × Bool) → ℝ) :
    (∑ x : ι → Fin 7, sixTensorMass p x * F (sixTripleAt p x t)) =
      ∑ z : ι → Bool × Bool × Bool, tensorTripleWeight p z * F z := by
  have h := product_expectation_pushforward
    (fun j r => (sixRootMass (p j) r : ℝ)) (fun j r => sixRootTriple (p j) t r) F
  dsimp only [productMass] at h
  simp_rw [sixRootTriple_real_fiber] at h
  exact h

#print axioms sixTensorMass_sum
#print axioms sixTensor_signature_expectation
#print axioms sixTensor_triangle_expectation

end
end Erdos883Second.Far
