import Erdos883SecondSignatureWeights
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators

def residuePrefixCount (n M r : ℕ) : ℕ :=
  Nat.count (fun x => (x + 1) % M = r) n

theorem count_period_mul (p : ℕ → Prop) [DecidablePred p] (M q : ℕ)
    (hper : Function.Periodic p M) : Nat.count p (q * M) = q * Nat.count p M := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add, ih]
    have he : (fun x => p (q * M + x)) = p := by
      funext x
      simpa only [Nat.cast_id, Nat.add_comm] using (hper.nat_mul q) x
    simp only [he]
    ring

theorem residue_pred_periodic (M r : ℕ) :
    Function.Periodic (fun x => (x + 1) % M = r) M := by
  intro x
  change ((x + M + 1) % M = r) = ((x + 1) % M = r)
  rw [show x + M + 1 = (x + 1) + M by omega, Nat.add_mod_right]

theorem residuePrefixCount_period (M r : ℕ) (hM : 0 < M) (hr : r < M) :
    residuePrefixCount M M r = 1 := by
  rw [residuePrefixCount, Nat.count_eq_card_filter_range]
  let a := if r = 0 then M - 1 else r - 1
  have ha : a < M := by dsimp [a]; split <;> omega
  apply Finset.card_eq_one.mpr
  refine ⟨a, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, he⟩
    by_cases hxM : x + 1 = M
    · rw [hxM, Nat.mod_self] at he
      dsimp [a]
      rw [if_pos he.symm]
      omega
    · have hxm : x + 1 < M := by omega
      rw [Nat.mod_eq_of_lt hxm] at he
      dsimp [a]
      rw [if_neg (by omega : r ≠ 0)]
      omega
  · intro he
    subst x
    refine ⟨ha, ?_⟩
    dsimp [a]
    split
    · next hz => rw [show M - 1 + 1 = M by omega, Nat.mod_self, hz]
    · next hz => rw [show r - 1 + 1 = r by omega, Nat.mod_eq_of_lt hr]

theorem residuePrefixCount_decomposition (n M r : ℕ) :
    residuePrefixCount n M r = n / M * residuePrefixCount M M r +
      residuePrefixCount (n % M) M r := by
  have hn : n = n / M * M + n % M := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod n M).symm
  conv_lhs => rw [hn]
  rw [residuePrefixCount, Nat.count_add,
    count_period_mul _ M (n / M) (residue_pred_periodic M r)]
  have he : (fun x => (n / M * M + x + 1) % M = r) =
      (fun x => (x + 1) % M = r) := by
    funext x
    simpa only [Nat.cast_id, Nat.add_comm (n / M * M) x] using
      (residue_pred_periodic M r).nat_mul (n / M) x
  simpa only [he, residuePrefixCount]

theorem residuePrefixCount_error (n M r : ℕ) (hM : 0 < M) (hr : r < M) :
    |(residuePrefixCount n M r : ℝ) - (n : ℝ) / M| ≤ 1 := by
  have hrM := Nat.mod_lt n hM
  have hc : residuePrefixCount (n % M) M r ≤ 1 := by
    have hh := Nat.count_monotone (fun x => (x + 1) % M = r) hrM.le
    change residuePrefixCount (n % M) M r ≤ residuePrefixCount M M r at hh
    rwa [residuePrefixCount_period M r hM hr] at hh
  have hdec := residuePrefixCount_decomposition n M r
  rw [residuePrefixCount_period M r hM hr, Nat.mul_one] at hdec
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hfrac0 : (0 : ℝ) ≤ (n % M : ℕ) / M := by positivity
  have hfrac1 : ((n % M : ℕ) : ℝ) / M ≤ 1 :=
    (div_le_one hMreal).mpr (by exact_mod_cast hrM.le)
  have hc0 : (0 : ℝ) ≤ residuePrefixCount (n % M) M r := by positivity
  have hc1 : (residuePrefixCount (n % M) M r : ℝ) ≤ 1 := by exact_mod_cast hc
  have hratio : (n : ℝ) / M = (n / M : ℕ) + ((n % M : ℕ) : ℝ) / M := by
    apply (div_eq_iff hMreal.ne').mpr
    have hh : (n : ℝ) = (M : ℝ) * (n / M : ℕ) + (n % M : ℕ) := by
      exact_mod_cast (Nat.div_add_mod n M).symm
    rw [add_mul, div_mul_cancel₀ _ hMreal.ne']
    nlinarith
  rw [hdec, Nat.cast_add, hratio]
  apply abs_le.mpr
  constructor <;> linarith

#print axioms residuePrefixCount_decomposition
#print axioms residuePrefixCount_error
end
end Erdos883Second.Signature
