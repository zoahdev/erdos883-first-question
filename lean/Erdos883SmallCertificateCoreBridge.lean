import Erdos883SmallCertificateCore
import Erdos883SmallCertificateEnrichedCheck
namespace Erdos883Verified

def oddDataOfCore (d : CoreOddData) : OddCertificateData :=
  ⟨d.value, d.factors, d.signatures⟩
def resourceOfCore (r : CoreResourceData) : PrefixResourceData :=
  ⟨r.q, r.s, r.bound, r.evenPool⟩

theorem corePrimeSieveCount_eq (X : ℕ) (ps : List ℕ) :
    corePrimeSieveCount X ps = fastPrimeSieveCount X ps := by
  induction ps generalizing X with
  | nil => rfl
  | cons p ps ih => simp only [corePrimeSieveCount, fastPrimeSieveCount, ih]

theorem coreDedup_eq (xs : List ℕ) : coreDedup xs = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [coreDedup, List.dedup_cons, ih]

theorem coreResourceRowCheck_eq (L : ℕ) (data : List CoreOddData)
    (r : CoreResourceData) (u : CoreOddData) :
    coreResourceRowCheck L data r u =
      enrichedResourceRowCheck L (data.map oddDataOfCore) (resourceOfCore r) (oddDataOfCore u) := by
  simp only [coreResourceRowCheck, enrichedResourceRowCheck, resourceOfCore,
    oddDataOfCore, ← List.map_take, List.all_map, Function.comp_def, corePrimeSieveCount_eq, coreDedup_eq]
  congr 1

theorem resourceRequirements_of_core {U : ℕ} {ps : List ℕ} {b j : ℕ} {r : CoreResourceData}
    (h : coreResourceRequirements U ps.length b j r) :
    ResourceRequirements U ps b j (resourceOfCore r) := h

theorem prefixResourceValid_extend_of_coreChunks {L : ℕ} {O ps : List ℕ}
    {data : List CoreOddData} {r : CoreResourceData} {C : ℕ} (q₀ K₀ : ℕ)
    (hdata : OddCertificateDataValid ps (data.map oddDataOfCore))
    (hmap : data.map (·.value) = O)
    (hs : r.s ≤ ps.length) (hqq : q₀ ≤ r.q) (hKK : r.bound ≤ K₀)
    (hprev : PrefixResourceValid L O ps ⟨q₀, r.s, K₀, r.evenPool⟩)
    (chunks : Fin C → List CoreOddData)
    (heq : (List.ofFn chunks).flatten = (data.take r.q).drop q₀)
    (hchecks : ∀ i, (chunks i).all (coreResourceRowCheck L data r) = true) :
    PrefixResourceValid L O ps (resourceOfCore r) := by
  apply prefixResourceValid_extend_of_enrichedChunks q₀ K₀ hdata
    (by simpa only [List.map_map, Function.comp_def, oddDataOfCore] using hmap)
    hs hqq hKK hprev (fun i => (chunks i).map oddDataOfCore)
  · change (List.ofFn (fun i => (chunks i).map oddDataOfCore)).flatten =
      ((data.map oddDataOfCore).take r.q).drop q₀
    rw [← List.map_take, ← List.map_drop, ← heq]
    simp only [List.map_flatten, List.map_ofFn, Function.comp_def]
  · intro i
    simpa only [List.all_map, Function.comp_def, ← coreResourceRowCheck_eq] using hchecks i

theorem coreNodup_eq_true (O : List ℕ) : coreNodup O = true ↔ O.Nodup := by
  induction O with
  | nil => simp [coreNodup]
  | cons a xs ih => simp [coreNodup, ih, List.nodup_cons]

theorem coreOrderCheck_sound {U : ℕ} {O : List ℕ} (h : coreOrderCheck U O = true) :
    O.Nodup ∧ O.toFinset = oddUniverse U := by
  simp only [coreOrderCheck, Bool.and_eq_true] at h
  have hnd := (coreNodup_eq_true O).mp h.1
  have hlen : O.length = halfOdds U := of_decide_eq_true h.2.1
  refine ⟨hnd, ?_⟩
  have hsub : O.toFinset ⊆ oddUniverse U := by
    intro v hv
    have hval := of_decide_eq_true (List.all_eq_true.mp h.2.2 v (List.mem_toFinset.mp hv))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hval.1, hval.2.1⟩,
      Nat.odd_iff.mpr hval.2.2⟩
  apply Finset.eq_of_subset_of_card_le hsub
  rw [List.toFinset_card_of_nodup hnd, oddUniverse_card, hlen]

theorem oddCertificateDataValid_of_coreChunks {ps : List ℕ} {data : List CoreOddData}
    {C : ℕ} (chunks : Fin C → List CoreOddData)
    (heq : (List.ofFn chunks).flatten = data)
    (hvalid : ∀ i, OddCertificateDataValid ps ((chunks i).map oddDataOfCore)) :
    OddCertificateDataValid ps (data.map oddDataOfCore) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  rw [← heq] at hc
  obtain ⟨chunk, hchunk, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchunk
  exact hvalid i (oddDataOfCore c) (List.mem_map.mpr ⟨c, hc, rfl⟩)

theorem corePrimeCheck_sound {p : ℕ} (h : corePrimeCheck p = true) : Nat.Prime p := by
  simp only [corePrimeCheck, Bool.and_eq_true] at h
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨of_decide_eq_true h.1, ?_⟩
  intro d hd hdsqrt hdvd
  have ht := of_decide_eq_true (List.all_eq_true.mp h.2 d (List.mem_range.mpr (by omega)))
  rcases ht with ht | ht
  · omega
  · exact ht (Nat.mod_eq_zero_of_dvd hdvd)

theorem coreDivisorSignature_eq (ps : List ℕ) (v : ℕ) :
    coreDivisorSignature ps v = divisorSignatureCode ps v := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [coreDivisorSignature, divisorSignatureCode, divisorSignatureBits,
      List.map_cons, binarySignatureCode, List.length_map] at ih ⊢
    rw [ih]
    simp [Nat.dvd_iff_mod_eq_zero]

theorem oddCertificateDataValid_of_coreCheck {ps : List ℕ} {data : List CoreOddData}
    (h : coreMetadataCheck ps data = true) :
    OddCertificateDataValid ps (data.map oddDataOfCore) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  have hf := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true] at hf
  refine ⟨of_decide_eq_true hf.1, ?_, Nat.odd_iff.mpr (of_decide_eq_true hf.2.2.1), ?_⟩
  · intro p hp
    exact corePrimeCheck_sound (List.all_eq_true.mp hf.2.1 p hp)
  · intro s
    have hs := of_decide_eq_true (List.all_eq_true.mp hf.2.2.2 s.val
      (List.mem_range.mpr s.isLt))
    simpa only [oddDataOfCore, coreDivisorSignature_eq] using hs

theorem coreMergeFuel_perm (fuel : ℕ) (xs ys : List ℕ) :
    (coreMergeFuel fuel xs ys).Perm (xs ++ ys) := by
  induction fuel generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    cases xs with
    | nil => simp [coreMergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [coreMergeFuel]
      | cons y ys =>
        simp only [coreMergeFuel]
        split
        · simpa only [List.cons_append] using List.Perm.cons x (ih xs (y :: ys))
        · have hmove : (y :: ((x :: xs) ++ ys)).Perm ((x :: xs) ++ y :: ys) := by
            simpa only [List.singleton_append, List.append_assoc, List.cons_append, List.nil_append] using
              (List.perm_append_comm (l₁ := [y]) (l₂ := x :: xs)).append_right ys
          exact (List.Perm.cons y (ih (x :: xs) ys)).trans hmove

theorem coreSortFuel_perm (fuel : ℕ) (xs : List ℕ) : (coreSortFuel fuel xs).Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    simpa only [coreSortFuel, List.take_append_drop] using
      (coreMergeFuel_perm xs.length (coreSortFuel fuel (xs.take (xs.length / 2)))
        (coreSortFuel fuel (xs.drop (xs.length / 2)))).trans
        ((ih (xs.take (xs.length / 2))).append (ih (xs.drop (xs.length / 2))))

theorem coreOrderPermutationCheck_sound {U : ℕ} {O : List ℕ}
    (h : coreOrderPermutationCheck U O = true) : O.Nodup ∧ O.toFinset = oddUniverse U := by
  have heq : coreSortFuel (Nat.log2 O.length + 1) O = List.range' 1 (coreHalfOdds U) 2 :=
    of_decide_eq_true h
  have hperm : O.Perm (List.range' 1 (coreHalfOdds U) 2) :=
    (coreSortFuel_perm (Nat.log2 O.length + 1) O).symm.trans (List.Perm.of_eq heq)
  refine ⟨hperm.nodup_iff.mpr (List.nodup_range' 2 (by decide)), ?_⟩
  ext v
  simp only [List.mem_toFinset, hperm.mem_iff, List.mem_range', oddUniverse,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold coreHalfOdds at hi
    exact ⟨⟨by omega, by omega⟩, ⟨i, by omega⟩⟩
  · rintro ⟨⟨hpos, hle⟩, ⟨i, hi⟩⟩
    refine ⟨i, ?_, by omega⟩
    unfold coreHalfOdds
    omega

#print axioms coreOrderPermutationCheck_sound

#print axioms corePrimeCheck_sound
#print axioms coreDivisorSignature_eq
#print axioms oddCertificateDataValid_of_coreCheck

#print axioms coreOrderCheck_sound
#print axioms oddCertificateDataValid_of_coreChunks

#print axioms corePrimeSieveCount_eq
#print axioms coreResourceRowCheck_eq
#print axioms resourceRequirements_of_core
#print axioms prefixResourceValid_extend_of_coreChunks
end Erdos883Verified
