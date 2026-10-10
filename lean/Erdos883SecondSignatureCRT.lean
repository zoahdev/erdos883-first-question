import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
An independently implemented arithmetic signature bridge. The CRT existence
construction is Mathlib's `Nat.chineseRemainderOfFinset` (rather than a
second-question proof). This module makes no graph-density assertion.
-/

namespace Erdos883Second.Signature

noncomputable section
open scoped BigOperators
open Function

def modulus (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

abbrev Residues (P : Finset ℕ) := (p : ↥P) → Fin (p : ℕ)
abbrev Bits (P : Finset ℕ) := ↥P → Bool

def residueMap (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (x : Fin (modulus P)) : Residues P :=
  fun p => ⟨(x : ℕ) % (p : ℕ), Nat.mod_lt _ (hp p p.property)⟩

theorem modulus_pos (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p) :
    0 < modulus P := Finset.prod_pos hp

theorem prod_subtype (P : Finset ℕ) :
    (∏ p : ↥P, (p : ℕ)) = modulus P := by
  exact Finset.prod_coe_sort P id

theorem residueMap_surjective (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) :
    Function.Surjective (residueMap P hp) := by
  intro y
  let a : ↥P → ℕ := fun p => (y p : ℕ)
  let m : ↥P → ℕ := fun p => (p : ℕ)
  have hm : ∀ p ∈ (Finset.univ : Finset ↥P), m p ≠ 0 := by
    intro p _
    exact (hp p p.property).ne'
  have hmc : Set.Pairwise ((Finset.univ : Finset ↥P) : Set ↥P)
      (Nat.Coprime on m) := by
    intro p _ q _ hpq
    exact hc p.property q.property (fun he => hpq (Subtype.ext he))
  let z := Nat.chineseRemainderOfFinset a m Finset.univ hm hmc
  have hz : (z : ℕ) < modulus P := by
    simpa only [m, prod_subtype] using
      Nat.chineseRemainderOfFinset_lt_prod a m hm hmc
  refine ⟨⟨z, hz⟩, ?_⟩
  funext p
  apply Fin.ext
  have he := z.property p (Finset.mem_univ p)
  change (z : ℕ) % (p : ℕ) = (y p : ℕ)
  simpa only [Nat.ModEq, a, m, Nat.mod_eq_of_lt (y p).isLt] using he

theorem residueMap_bijective (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) :
    Function.Bijective (residueMap P hp) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨residueMap_surjective P hp hc, ?_⟩
  simp only [Residues, Fintype.card_pi, Fintype.card_fin, prod_subtype]

def crtEquiv (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) :
    Fin (modulus P) ≃ Residues P :=
  Equiv.ofBijective (residueMap P hp) (residueMap_bijective P hp hc)

theorem primes_pairwise_coprime (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) : Set.Pairwise (P : Set ℕ) Nat.Coprime := by
  intro p hpP q hqP hpq
  exact ((hp p hpP).coprime_iff_not_dvd).mpr (by
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq (hp p hpP) (hp q hqP)).mp hd))

def signature (P : Finset ℕ) (x : ℕ) : Bits P :=
  fun p => decide ((p : ℕ) ∣ x)

def residueBits (P : Finset ℕ) (y : Residues P) : Bits P :=
  fun p => decide ((y p : ℕ) = 0)

theorem residueMap_bits (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (x : Fin (modulus P)) :
    residueBits P (residueMap P hp x) = signature P x := by
  funext p
  simp only [residueBits, residueMap, signature, Nat.dvd_iff_mod_eq_zero]
  rfl

#print axioms residueMap_bijective
#print axioms residueMap_bits

end
end Erdos883Second.Signature
