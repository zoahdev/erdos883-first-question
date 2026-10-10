import Erdos883SecondSignatureCRT
import Erdos883SecondSpectralBasis
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators

def coordinateMultiplicity (p : ℕ) (b : Bool) : ℕ := if b then 1 else p - 1

def periodCount (P : Finset ℕ) (s : Bits P) : ℕ :=
  Fintype.card {x : Fin (modulus P) // signature P x = s}

def productWeight (P : Finset ℕ) (s : Bits P) : ℝ :=
  Erdos883.SecondSpectral.tensorWeight (fun p : ↥P => (p : ℕ)) s

theorem coordinate_card (p : ℕ) (hp : 0 < p) (b : Bool) :
    Fintype.card {r : Fin p // decide ((r : ℕ) = 0) = b} =
      coordinateMultiplicity p b := by
  let z : Fin p := ⟨0, hp⟩
  have hz (r : Fin p) : (r : ℕ) = 0 ↔ r = z := by
    constructor
    · exact fun he => Fin.ext he
    · exact fun he => congrArg Fin.val he
  have hzero : Fintype.card {r : Fin p // (r : ℕ) = 0} = 1 := by
    exact (Fintype.card_congr
      ((Equiv.refl (Fin p)).subtypeEquiv hz)).trans (Fintype.card_subtype_eq z)
  cases b
  · simp only [decide_eq_false_iff_not, coordinateMultiplicity, Bool.false_eq_true,
      ↓reduceIte]
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hzero]
  · simpa only [decide_eq_true_eq, coordinateMultiplicity, Bool.true_eq,
      ↓reduceIte] using hzero

theorem periodCount_eq_product (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) (s : Bits P) :
    periodCount P s = ∏ p : ↥P, coordinateMultiplicity p (s p) := by
  let e := crtEquiv P hp hc
  let e1 : {x : Fin (modulus P) // signature P x = s} ≃
      {y : Residues P // residueBits P y = s} :=
    e.subtypeEquiv (fun x => by
      change signature P x = s ↔ residueBits P (residueMap P hp x) = s
      rw [residueMap_bits])
  let e2 : {y : Residues P // residueBits P y = s} ≃
      {y : Residues P // ∀ p, decide ((y p : ℕ) = 0) = s p} :=
    (Equiv.refl _).subtypeEquiv (fun y => by
      change residueBits P y = s ↔ ∀ p, residueBits P y p = s p
      exact funext_iff)
  let e3 : {y : Residues P // ∀ p, decide ((y p : ℕ) = 0) = s p} ≃
      ((p : ↥P) → {r : Fin (p : ℕ) // decide ((r : ℕ) = 0) = s p}) :=
    @Equiv.subtypePiEquivPi ↥P (fun p => Fin (p : ℕ))
      (fun p r => decide ((r : ℕ) = 0) = s p)
  rw [periodCount, Fintype.card_congr (e1.trans (e2.trans e3)),
    Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro p _
  exact coordinate_card p (hp p p.property) (s p)

theorem coordinateMultiplicity_div (p : ℕ) (hp : 0 < p) (b : Bool) :
    (coordinateMultiplicity p b : ℝ) / p =
      Erdos883.SecondSpectral.coordinateWeight (p : ℝ) b := by
  cases b
  · simp only [coordinateMultiplicity, Bool.false_eq_true, ↓reduceIte,
      Erdos883.SecondSpectral.coordinateWeight, Nat.cast_sub (by omega : 1 ≤ p),
      Nat.cast_one]
  · simp [coordinateMultiplicity, Erdos883.SecondSpectral.coordinateWeight]

theorem periodCount_div_modulus (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) (s : Bits P) :
    (periodCount P s : ℝ) / modulus P = productWeight P s := by
  rw [periodCount_eq_product P hp hc, ← prod_subtype]
  simp only [Nat.cast_prod, productWeight,
    Erdos883.SecondSpectral.tensorWeight]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  exact coordinateMultiplicity_div p (hp p p.property) (s p)

#print axioms periodCount_eq_product
#print axioms periodCount_div_modulus
end
end Erdos883Second.Signature
