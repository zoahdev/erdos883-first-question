import Erdos883FiniteCheck

namespace Erdos883Verified

/-- An explicit lower bound for same-signature pairs in an ambient prefix. -/
def prefixResourceBound (P : Finset ℕ) (O ps : List ℕ) (q K : ℕ) : Prop :=
  ∀ u ∈ orderPrefix O q, ∀ v ∈ orderPrefix O q, u ≠ v →
    divisorSignatureCode ps u = divisorSignatureCode ps v →
      K ≤ (rawCommon Nat.Coprime P u v).card

theorem prefixResourceBound_mono {P : Finset ℕ} {O ps : List ℕ} {p q K H : ℕ}
    (hpq : p ≤ q) (hHK : H ≤ K) (h : prefixResourceBound P O ps q K) :
    prefixResourceBound P O ps p H := by
  intro u hu v hv hne hsig
  have hsub : orderPrefix O p ⊆ orderPrefix O q := by
    intro x hx
    simp only [orderPrefix, List.mem_toFinset] at hx ⊢
    exact List.take_subset_take_left O hpq hx
  exact hHK.trans (h u (hsub hu) v (hsub hv) hne hsig)

/-- Untrusted compact resource data; validity is separately proved in the kernel. -/
structure PrefixResourceData where
  q : ℕ
  s : ℕ
  bound : ℕ
  evenPool : Bool

def PrefixResourceValid (L : ℕ) (O ps : List ℕ) (r : PrefixResourceData) : Prop :=
  prefixResourceBound (if r.evenPool then evenUniverse L else Finset.Icc 1 L)
    O (ps.take r.s) r.q r.bound

def ResourceRequirements (U : ℕ) (ps : List ℕ) (b j : ℕ)
    (r : PrefixResourceData) : Prop :=
  let p := halfOdds U - b - (j - signatureBudget r.s - 1) / 2
  r.s ≤ ps.length ∧ p ≤ halfOdds U ∧ p ≤ r.q ∧
    2 * (halfOdds U - p - b) + signatureBudget r.s < j ∧
    (if r.evenPool then b + j else U - threshold U + maxHalfLength U + j) ≤ r.bound

theorem intervalWitness_of_resource {L U : ℕ} {O ps : List ℕ} {b j : ℕ}
    {r : PrefixResourceData} (hvalid : PrefixResourceValid L O ps r)
    (hreq : ResourceRequirements U ps b j r) :
    intervalWitness L U O ps b j r.s := by
  rcases hreq with ⟨hs, hp, hpq, hbudget, hK⟩
  refine ⟨hp, hbudget, ?_⟩
  cases he : r.evenPool
  · apply Or.inr
    simp only [PrefixResourceValid, he, Bool.false_eq_true, if_false] at hvalid
    simp only [he, Bool.false_eq_true, if_false] at hK
    exact prefixResourceBound_mono hpq hK hvalid
  · apply Or.inl
    simp only [PrefixResourceValid, he, if_true] at hvalid
    simp only [he, if_true] at hK
    exact prefixResourceBound_mono hpq hK hvalid

theorem finiteIntervalCheck_of_resources {L U : ℕ} {O ps : List ℕ} {R : ℕ}
    (resources : Fin R → PrefixResourceData)
    (selector : Fin (halfOdds U - retainedOdds U + 1) →
      Fin (maxHalfLength U) → Fin R)
    (hvalid : ∀ i, PrefixResourceValid L O ps (resources i))
    (hreq : ∀ b j, ResourceRequirements U ps b.val (j.val + 1)
      (resources (selector b j))) : finiteIntervalCheck L U O ps := by
  intro b j
  have h := hreq b j
  refine ⟨⟨(resources (selector b j)).s, by have := h.1; omega⟩, ?_⟩
  exact intervalWitness_of_resource (hvalid (selector b j)) h

#print axioms prefixResourceBound_mono
#print axioms intervalWitness_of_resource
#print axioms finiteIntervalCheck_of_resources
end Erdos883Verified
