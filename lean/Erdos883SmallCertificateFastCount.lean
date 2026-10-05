import Erdos883SmallCertificateListCheck
namespace Erdos883Verified

def listCountAtLeast {α : Type*} (p : α → Bool) : ℕ → List α → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | k + 1, x :: xs => if p x then listCountAtLeast p k xs else listCountAtLeast p (k + 1) xs

theorem listCountAtLeast_sound {α : Type*} {p : α → Bool} {K : ℕ} {xs : List α}
    (h : listCountAtLeast p K xs = true) : K ≤ (xs.filter p).length := by
  induction xs generalizing K with
  | nil => cases K <;> simp_all [listCountAtLeast]
  | cons x xs ih =>
    cases K with
    | zero => omega
    | succ K =>
      cases hp : p x
      · simp only [listCountAtLeast, hp, Bool.false_eq_true, if_false] at h
        simpa [hp] using ih h
      · simp only [listCountAtLeast, hp, if_true] at h
        simpa [hp] using Nat.succ_le_succ (ih h)

def explicitResourcePool (L : ℕ) (evenPool : Bool) : List ℕ :=
  if evenPool then List.range' 2 (L / 2) 2 else List.range' 1 L

theorem explicitResourcePool_nodup (L : ℕ) (evenPool : Bool) :
    (explicitResourcePool L evenPool).Nodup := by
  cases evenPool <;> simp [explicitResourcePool, List.nodup_range']

theorem explicitResourcePool_subset (L : ℕ) (evenPool : Bool) :
    (explicitResourcePool L evenPool).toFinset ⊆
      (if evenPool then evenUniverse L else Finset.Icc 1 L) := by
  intro w hw
  cases evenPool
  · simp only [explicitResourcePool, Bool.false_eq_true, if_false, List.mem_toFinset,
      List.mem_range'_1] at hw
    exact Finset.mem_Icc.mpr ⟨hw.1, by omega⟩
  · simp only [explicitResourcePool, if_true, List.mem_toFinset, List.mem_range'] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨i + 1, by omega⟩⟩

theorem rawCommon_lower_of_listCountAtLeast {L u v K : ℕ} {evenPool : Bool}
    (h : listCountAtLeast (fun w => decide (Nat.Coprime w u ∧ Nat.Coprime w v)) K
      (explicitResourcePool L evenPool) = true) :
    K ≤ (rawCommon Nat.Coprime
      (if evenPool then evenUniverse L else Finset.Icc 1 L) u v).card := by
  have hlen := listCountAtLeast_sound h
  have hnd := (explicitResourcePool_nodup L evenPool).filter
    (fun w => decide (Nat.Coprime w u ∧ Nat.Coprime w v))
  have hsub : ((explicitResourcePool L evenPool).filter
      (fun w => decide (Nat.Coprime w u ∧ Nat.Coprime w v))).toFinset ⊆
      rawCommon Nat.Coprime (if evenPool then evenUniverse L else Finset.Icc 1 L) u v := by
    intro w hw
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
    exact Finset.mem_filter.mpr ⟨explicitResourcePool_subset L evenPool
      (List.mem_toFinset.mpr hw.1), hw.2⟩
  calc
    K ≤ ((explicitResourcePool L evenPool).filter
        (fun w => decide (Nat.Coprime w u ∧ Nat.Coprime w v))).length := hlen
    _ = _ := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ _ := Finset.card_le_card hsub

def fastPrefixResourceCheck (L : ℕ) (O ps : List ℕ) (r : PrefixResourceData) : Bool :=
  (O.take r.q).all fun u => (O.take r.q).all fun v =>
    decide (u = v ∨ divisorSignatureCode (ps.take r.s) u ≠
      divisorSignatureCode (ps.take r.s) v) ||
    listCountAtLeast (fun w => decide (Nat.Coprime w u ∧ Nat.Coprime w v)) r.bound
      (explicitResourcePool L r.evenPool)

theorem prefixResourceValid_of_fastCheck {L : ℕ} {O ps : List ℕ} {r : PrefixResourceData}
    (h : fastPrefixResourceCheck L O ps r = true) : PrefixResourceValid L O ps r := by
  intro u hu v hv hne hsig
  unfold fastPrefixResourceCheck at h
  have hu' : u ∈ O.take r.q := by simpa only [orderPrefix, List.mem_toFinset] using hu
  have hv' : v ∈ O.take r.q := by simpa only [orderPrefix, List.mem_toFinset] using hv
  have hpair := List.all_eq_true.mp (List.all_eq_true.mp h u hu') v hv'
  rcases Bool.or_eq_true_iff.mp hpair with hskip | hcount
  · rcases of_decide_eq_true hskip with h | h
    · exact False.elim (hne h)
    · exact False.elim (h hsig)
  · exact rawCommon_lower_of_listCountAtLeast hcount

/-- Triangular checking removes the duplicate orientation of every endpoint pair. -/
def triangularPrefixResourceCheck (L : ℕ) (O ps : List ℕ)
    (r : PrefixResourceData) : Bool :=
  (O.take r.q).all fun u => (O.take r.q).all fun v =>
    decide (v ≤ u ∨ divisorSignatureCode (ps.take r.s) u ≠
      divisorSignatureCode (ps.take r.s) v) ||
    listCountAtLeast (fun w => decide (Nat.Coprime w u ∧ Nat.Coprime w v)) r.bound
      (explicitResourcePool L r.evenPool)

theorem prefixResourceValid_of_triangularCheck {L : ℕ} {O ps : List ℕ}
    {r : PrefixResourceData} (h : triangularPrefixResourceCheck L O ps r = true) :
    PrefixResourceValid L O ps r := by
  have hlt : ∀ u ∈ orderPrefix O r.q, ∀ v ∈ orderPrefix O r.q, u < v →
      divisorSignatureCode (ps.take r.s) u = divisorSignatureCode (ps.take r.s) v →
      r.bound ≤ (rawCommon Nat.Coprime
        (if r.evenPool then evenUniverse L else Finset.Icc 1 L) u v).card := by
    intro u hu v hv huv hsig
    unfold triangularPrefixResourceCheck at h
    have hu' : u ∈ O.take r.q := by simpa only [orderPrefix, List.mem_toFinset] using hu
    have hv' : v ∈ O.take r.q := by simpa only [orderPrefix, List.mem_toFinset] using hv
    have hpair := List.all_eq_true.mp (List.all_eq_true.mp h u hu') v hv'
    rcases Bool.or_eq_true_iff.mp hpair with hskip | hcount
    · rcases of_decide_eq_true hskip with hle | hne
      · omega
      · exact False.elim (hne hsig)
    · exact rawCommon_lower_of_listCountAtLeast hcount
  intro u hu v hv hne hsig
  by_cases huv : u < v
  · exact hlt u hu v hv huv hsig
  · have hswap := hlt v hv u hu (by omega) hsig.symm
    have heq : rawCommon Nat.Coprime
        (if r.evenPool then evenUniverse L else Finset.Icc 1 L) v u =
        rawCommon Nat.Coprime
        (if r.evenPool then evenUniverse L else Finset.Icc 1 L) u v := by
      ext w
      simp only [rawCommon, Finset.mem_filter, and_comm]
    simpa only [heq] using hswap

#print axioms prefixResourceValid_of_triangularCheck

#print axioms listCountAtLeast_sound
#print axioms explicitResourcePool_subset
#print axioms rawCommon_lower_of_listCountAtLeast
#print axioms prefixResourceValid_of_fastCheck
end Erdos883Verified
