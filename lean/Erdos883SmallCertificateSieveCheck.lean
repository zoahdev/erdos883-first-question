import Erdos883SmallCertificateFactors
import Erdos883PrimeSieveCount
namespace Erdos883Verified

def FactorDataValid (O : List ℕ) (factors : ℕ → List ℕ) : Prop :=
  ∀ u ∈ O, (factors u).prod = u ∧ (∀ p ∈ factors u, Nat.Prime p) ∧ Odd u

def sievePrefixResourceCheck (L : ℕ) (O ps : List ℕ) (factors : ℕ → List ℕ)
    (r : PrefixResourceData) : Bool :=
  (O.take r.q).all fun u => (O.take r.q).all fun v =>
    decide (v ≤ u ∨ divisorSignatureCode (ps.take r.s) u ≠
      divisorSignatureCode (ps.take r.s) v ∨
      r.bound ≤ fastPrimeSieveCount (if r.evenPool then L / 2 else L)
        ((factors u ++ factors v).dedup))

theorem prefixResourceValid_of_sieveCheck {L : ℕ} {O ps : List ℕ}
    {factors : ℕ → List ℕ} {r : PrefixResourceData}
    (hf : FactorDataValid O factors)
    (h : sievePrefixResourceCheck L O ps factors r = true) :
    PrefixResourceValid L O ps r := by
  have hlt : ∀ u ∈ orderPrefix O r.q, ∀ v ∈ orderPrefix O r.q, u < v →
      divisorSignatureCode (ps.take r.s) u = divisorSignatureCode (ps.take r.s) v →
      r.bound ≤ (rawCommon Nat.Coprime
        (if r.evenPool then evenUniverse L else Finset.Icc 1 L) u v).card := by
    intro u hu v hv huv hsig
    unfold sievePrefixResourceCheck at h
    have hu' : u ∈ O.take r.q := by simpa only [orderPrefix, List.mem_toFinset] using hu
    have hv' : v ∈ O.take r.q := by simpa only [orderPrefix, List.mem_toFinset] using hv
    have hpair := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h u hu') v hv')
    rcases hpair with hle | hne | hcount
    · omega
    · exact False.elim (hne hsig)
    · obtain ⟨huprod, huprime, huodd⟩ := hf u (List.take_subset _ _ hu')
      obtain ⟨hvprod, hvprime, hvodd⟩ := hf v (List.take_subset _ _ hv')
      have hp : ∀ p ∈ (factors u ++ factors v).dedup, Nat.Prime p := by
        intro p hp
        simp only [List.mem_dedup, List.mem_append] at hp
        rcases hp with hp | hp
        · exact huprime p hp
        · exact hvprime p hp
      rw [fastPrimeSieveCount_eq_coprimePrefixCount _ (List.nodup_dedup _) hp] at hcount
      rw [factorized_rawCommon_card L r.evenPool huprod hvprod huodd hvodd]
      exact hcount
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

def sieveResourceRowCheck (L : ℕ) (O ps : List ℕ) (factors : ℕ → List ℕ)
    (r : PrefixResourceData) (u : ℕ) : Bool :=
  (O.take r.q).all fun v =>
    decide (v ≤ u ∨ divisorSignatureCode (ps.take r.s) u ≠
      divisorSignatureCode (ps.take r.s) v ∨
      r.bound ≤ fastPrimeSieveCount (if r.evenPool then L / 2 else L)
        ((factors u ++ factors v).dedup))

/-- Independently kernel-checked row batches assemble without repeating the count reductions. -/
theorem prefixResourceValid_of_sieveChunks {L : ℕ} {O ps : List ℕ}
    {factors : ℕ → List ℕ} {r : PrefixResourceData} {C : ℕ}
    (hf : FactorDataValid O factors) (chunks : Fin C → List ℕ)
    (heq : (List.ofFn chunks).flatten = O.take r.q)
    (hchecks : ∀ i, (chunks i).all (sieveResourceRowCheck L O ps factors r) = true) :
    PrefixResourceValid L O ps r := by
  apply prefixResourceValid_of_sieveCheck hf
  change (O.take r.q).all (sieveResourceRowCheck L O ps factors r) = true
  apply List.all_eq_true.mpr
  intro u hu
  rw [← heq] at hu
  obtain ⟨chunk, hchunk, hu⟩ := List.mem_flatten.mp hu
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchunk
  exact List.all_eq_true.mp (hchecks i) u hu

/-- Enlarging a prefix only requires checking pairs with a newly added endpoint. -/
theorem prefixResourceBound_extend {P : Finset ℕ} {O ps : List ℕ}
    {q₀ q K₀ K : ℕ} (hqq : q₀ ≤ q) (hKK : K ≤ K₀)
    (hprev : prefixResourceBound P O ps q₀ K₀)
    (hnew : ∀ u ∈ (O.take q).drop q₀, ∀ v ∈ O.take q, u ≠ v →
      divisorSignatureCode ps u = divisorSignatureCode ps v →
        K ≤ (rawCommon Nat.Coprime P u v).card) : prefixResourceBound P O ps q K := by
  have hdecomp : O.take q = O.take q₀ ++ (O.take q).drop q₀ := by
    simpa only [List.take_take, Nat.min_eq_left hqq] using
      (List.take_append_drop q₀ (O.take q)).symm
  intro u hu v hv hne hsig
  have hu' : u ∈ O.take q := by simpa only [orderPrefix, List.mem_toFinset] using hu
  have hv' : v ∈ O.take q := by simpa only [orderPrefix, List.mem_toFinset] using hv
  have huCases : u ∈ O.take q₀ ∨ u ∈ (O.take q).drop q₀ := by
    rw [hdecomp, List.mem_append] at hu'
    exact hu'
  have hvCases : v ∈ O.take q₀ ∨ v ∈ (O.take q).drop q₀ := by
    rw [hdecomp, List.mem_append] at hv'
    exact hv'
  rcases huCases with huOld | huNew
  · rcases hvCases with hvOld | hvNew
    · exact hKK.trans (hprev u (List.mem_toFinset.mpr huOld)
        v (List.mem_toFinset.mpr hvOld) hne hsig)
    · have hswap := hnew v hvNew u hu' hne.symm hsig.symm
      have heq : rawCommon Nat.Coprime P v u = rawCommon Nat.Coprime P u v := by
        ext w
        simp only [rawCommon, Finset.mem_filter, and_comm]
      simpa only [heq] using hswap
  · exact hnew u huNew v hv' hne hsig

def sieveResourceFullRowCheck (L : ℕ) (O ps : List ℕ) (factors : ℕ → List ℕ)
    (r : PrefixResourceData) (u : ℕ) : Bool :=
  (O.take r.q).all fun v =>
    decide (u = v ∨ divisorSignatureCode (ps.take r.s) u ≠
      divisorSignatureCode (ps.take r.s) v ∨
      r.bound ≤ fastPrimeSieveCount (if r.evenPool then L / 2 else L)
        ((factors u ++ factors v).dedup))

theorem prefixResourceValid_extend_of_sieveRows {L : ℕ} {O ps : List ℕ}
    {factors : ℕ → List ℕ} {r : PrefixResourceData} (q₀ K₀ : ℕ)
    (hf : FactorDataValid O factors) (hqq : q₀ ≤ r.q) (hKK : r.bound ≤ K₀)
    (hprev : PrefixResourceValid L O ps ⟨q₀, r.s, K₀, r.evenPool⟩)
    (hchecks : ∀ u ∈ (O.take r.q).drop q₀,
      sieveResourceFullRowCheck L O ps factors r u = true) :
    PrefixResourceValid L O ps r := by
  apply prefixResourceBound_extend hqq hKK hprev
  intro u hu v hv hne hsig
  have hu' : u ∈ O := List.take_subset _ _ (List.mem_of_mem_drop hu)
  have hv' : v ∈ O := List.take_subset _ _ hv
  have hpair := of_decide_eq_true (List.all_eq_true.mp (hchecks u hu) v hv)
  rcases hpair with heq | hsig' | hcount
  · exact False.elim (hne heq)
  · exact False.elim (hsig' hsig)
  · obtain ⟨huprod, huprime, huodd⟩ := hf u hu'
    obtain ⟨hvprod, hvprime, hvodd⟩ := hf v hv'
    have hp : ∀ p ∈ (factors u ++ factors v).dedup, Nat.Prime p := by
      intro p hp
      simp only [List.mem_dedup, List.mem_append] at hp
      rcases hp with hp | hp
      · exact huprime p hp
      · exact hvprime p hp
    rw [fastPrimeSieveCount_eq_coprimePrefixCount _ (List.nodup_dedup _) hp] at hcount
    rw [factorized_rawCommon_card L r.evenPool huprod hvprod huodd hvodd]
    exact hcount

/-- Reuse an earlier resource certificate and check only new rows, in bounded batches. -/
theorem prefixResourceValid_extend_of_sieveChunks {L : ℕ} {O ps : List ℕ}
    {factors : ℕ → List ℕ} {r : PrefixResourceData} {C : ℕ} (q₀ K₀ : ℕ)
    (hf : FactorDataValid O factors) (hqq : q₀ ≤ r.q) (hKK : r.bound ≤ K₀)
    (hprev : PrefixResourceValid L O ps ⟨q₀, r.s, K₀, r.evenPool⟩)
    (chunks : Fin C → List ℕ)
    (heq : (List.ofFn chunks).flatten = (O.take r.q).drop q₀)
    (hchecks : ∀ i, (chunks i).all (sieveResourceFullRowCheck L O ps factors r) = true) :
    PrefixResourceValid L O ps r := by
  apply prefixResourceValid_extend_of_sieveRows q₀ K₀ hf hqq hKK hprev
  intro u hu
  rw [← heq] at hu
  obtain ⟨chunk, hchunk, hu⟩ := List.mem_flatten.mp hu
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchunk
  exact List.all_eq_true.mp (hchecks i) u hu

#print axioms prefixResourceBound_extend
#print axioms prefixResourceValid_extend_of_sieveRows
#print axioms prefixResourceValid_extend_of_sieveChunks

#print axioms prefixResourceValid_of_sieveChunks

#print axioms prefixResourceValid_of_sieveCheck
end Erdos883Verified
