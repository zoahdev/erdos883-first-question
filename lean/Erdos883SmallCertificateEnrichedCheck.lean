import Erdos883SmallCertificateSieveCheck
namespace Erdos883Verified

/-- Cached arithmetic metadata, never trusted without its validity proof. -/
structure OddCertificateData where
  value : ℕ
  factors : List ℕ
  signatures : List ℕ
  deriving DecidableEq

def OddCertificateDataValid (ps : List ℕ) (data : List OddCertificateData) : Prop :=
  ∀ d ∈ data, d.factors.prod = d.value ∧ (∀ p ∈ d.factors, Nat.Prime p) ∧ Odd d.value ∧
    ∀ s : Fin (ps.length + 1), d.signatures.getD s.val 0 =
      divisorSignatureCode (ps.take s.val) d.value

def enrichedResourceRowCheck (L : ℕ) (data : List OddCertificateData)
    (r : PrefixResourceData) (u : OddCertificateData) : Bool :=
  (data.take r.q).all fun v =>
    decide (u.value = v.value ∨ u.signatures.getD r.s 0 ≠ v.signatures.getD r.s 0 ∨
      r.bound ≤ fastPrimeSieveCount (if r.evenPool then L / 2 else L)
        ((u.factors ++ v.factors).dedup))

theorem prefixResourceValid_extend_of_enrichedChunks {L : ℕ} {O ps : List ℕ}
    {data : List OddCertificateData} {r : PrefixResourceData} {C : ℕ} (q₀ K₀ : ℕ)
    (hdata : OddCertificateDataValid ps data) (hmap : data.map (·.value) = O)
    (hs : r.s ≤ ps.length) (hqq : q₀ ≤ r.q) (hKK : r.bound ≤ K₀)
    (hprev : PrefixResourceValid L O ps ⟨q₀, r.s, K₀, r.evenPool⟩)
    (chunks : Fin C → List OddCertificateData)
    (heq : (List.ofFn chunks).flatten = (data.take r.q).drop q₀)
    (hchecks : ∀ i, (chunks i).all (enrichedResourceRowCheck L data r) = true) :
    PrefixResourceValid L O ps r := by
  apply prefixResourceBound_extend hqq hKK hprev
  intro u hu v hv hne hsig
  have huMap : u ∈ ((data.take r.q).drop q₀).map (·.value) := by
    simpa only [← hmap, List.map_take, List.map_drop] using hu
  have hvMap : v ∈ (data.take r.q).map (·.value) := by
    simpa only [← hmap, List.map_take] using hv
  obtain ⟨du, hdu, rfl⟩ := List.mem_map.mp huMap
  obtain ⟨dv, hdv, rfl⟩ := List.mem_map.mp hvMap
  have hrow : enrichedResourceRowCheck L data r du = true := by
    rw [← heq] at hdu
    obtain ⟨chunk, hchunk, hdu⟩ := List.mem_flatten.mp hdu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchunk
    exact List.all_eq_true.mp (hchecks i) du hdu
  have hpair := of_decide_eq_true (List.all_eq_true.mp hrow dv hdv)
  obtain ⟨huprod, huprime, huodd, husig⟩ := hdata du
    (List.take_subset _ _ (List.mem_of_mem_drop hdu))
  obtain ⟨hvprod, hvprime, hvodd, hvsig⟩ := hdata dv (List.take_subset _ _ hdv)
  rcases hpair with heq | hsig' | hcount
  · exact False.elim (hne heq)
  · exact False.elim (hsig' (by
      rw [husig ⟨r.s, by omega⟩, hvsig ⟨r.s, by omega⟩]
      exact hsig))
  · have hp : ∀ p ∈ (du.factors ++ dv.factors).dedup, Nat.Prime p := by
      intro p hp
      simp only [List.mem_dedup, List.mem_append] at hp
      rcases hp with hp | hp
      · exact huprime p hp
      · exact hvprime p hp
    rw [fastPrimeSieveCount_eq_coprimePrefixCount _ (List.nodup_dedup _) hp] at hcount
    rw [factorized_rawCommon_card L r.evenPool huprod hvprod huodd hvodd]
    exact hcount

theorem prefixResourceValid_empty (L : ℕ) (O ps : List ℕ) (s K : ℕ) (evenPool : Bool) :
    PrefixResourceValid L O ps ⟨0, s, K, evenPool⟩ := by
  simp [PrefixResourceValid, prefixResourceBound, orderPrefix]

#print axioms prefixResourceValid_empty

#print axioms prefixResourceValid_extend_of_enrichedChunks
end Erdos883Verified
