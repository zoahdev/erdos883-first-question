import Erdos883SecondCouplingNorm
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Prime

/-! A finite six-position coupling at each prime >=5. At prime 5 only
positions 1 and 6 coincide; at larger primes the six positions are distinct.
This abstract root law replaces a residue-variable presentation and has
exactly the required marginal and seven triangle laws. -/

namespace Erdos883Second.Far

open scoped BigOperators

def sixRootMass (p : ℕ) (j : Fin 7) : ℚ :=
  if p = 5 then (if j.val < 5 then 1 / p else 0)
  else if j.val < 6 then 1 / p else 1 - 6 / p

def sixRootBit (p : ℕ) (j : Fin 7) (i : Fin 6) : Bool :=
  if p = 5 then decide (j.val = i.val ∨ (j.val = 0 ∧ i.val = 5))
  else decide (j.val = i.val)

def sixTriple (t : Fin 7) : Fin 6 × Fin 6 × Fin 6 :=
  match t.val with
  | 0 => (0, 2, 4)
  | 1 => (1, 0, 2)
  | 2 => (1, 0, 4)
  | 3 => (1, 2, 4)
  | 4 => (3, 0, 2)
  | 5 => (3, 0, 4)
  | _ => (3, 2, 4)

def sixRootTriple (p : ℕ) (t j : Fin 7) : Bool × Bool × Bool :=
  (sixRootBit p j (sixTriple t).1,
   sixRootBit p j (sixTriple t).2.1,
   sixRootBit p j (sixTriple t).2.2)

theorem sixRootMass_sum (p : ℕ) : (∑ j : Fin 7, sixRootMass p j) = 1 := by
  by_cases hp : p = 5
  · subst p
    norm_num [sixRootMass, Fin.sum_univ_succ]
  · simp [sixRootMass, hp, Fin.sum_univ_succ]
    ring

theorem sixRootMass_nonneg {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (j : Fin 7) :
    0 ≤ sixRootMass p j := by
  by_cases he : p = 5
  · subst p
    simp only [sixRootMass, if_true]
    split_ifs <;> norm_num
  · have hp6 : p ≠ 6 := by intro h; subst p; norm_num at hp
    have hp7 : 7 ≤ p := by omega
    have hpq : (7 : ℚ) ≤ p := by exact_mod_cast hp7
    have hdiv : (6 : ℚ) / p ≤ 1 :=
      (div_le_iff₀ (by linarith : (0 : ℚ) < p)).mpr (by linarith)
    simp only [sixRootMass, if_neg he]
    split_ifs
    · positivity
    · linarith

theorem sixRootBit_marginal (p : ℕ) (i : Fin 6) (b : Bool) :
    (∑ j : Fin 7, if sixRootBit p j i = b then sixRootMass p j else 0) =
      bernoulliMass (1 / p) b := by
  by_cases hp : p = 5
  · subst p
    fin_cases i <;> cases b <;>
      norm_num [sixRootBit, sixRootMass, bernoulliMass, Fin.sum_univ_succ]
  · fin_cases i <;> cases b <;>
      simp [sixRootBit, sixRootMass, bernoulliMass, hp, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem sixRootTriple_marginal (p : ℕ) (t : Fin 7) (z : Bool × Bool × Bool) :
    (∑ j : Fin 7, if sixRootTriple p t j = z then sixRootMass p j else 0) =
      disjointTripleMass (1 / p) z := by
  rcases z with ⟨a, b, c⟩
  by_cases hp : p = 5
  · subst p
    fin_cases t <;> cases a <;> cases b <;> cases c <;>
      norm_num [sixRootTriple, sixTriple, sixRootBit, sixRootMass,
        disjointTripleMass, Fin.sum_univ_succ]
  · fin_cases t <;> cases a <;> cases b <;> cases c <;>
      simp [sixRootTriple, sixTriple, sixRootBit, sixRootMass,
        disjointTripleMass, hp, Fin.sum_univ_succ] <;> ring

#print axioms sixRootMass_sum
#print axioms sixRootMass_nonneg
#print axioms sixRootBit_marginal
#print axioms sixRootTriple_marginal

end Erdos883Second.Far
