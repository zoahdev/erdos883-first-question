import Erdos883SmallCertificateHelpers
namespace Erdos883Verified

/-- List recursion avoids proof-carrying finite universal decision overhead. -/
def prefixResourceListCheck (P : Finset ℕ) (O ps : List ℕ) (q K : ℕ) : Bool :=
  (O.take q).all fun u => (O.take q).all fun v =>
    decide (u = v ∨ divisorSignatureCode ps u ≠ divisorSignatureCode ps v ∨
      K ≤ (rawCommon Nat.Coprime P u v).card)

theorem prefixResourceBound_of_listCheck {P : Finset ℕ} {O ps : List ℕ} {q K : ℕ}
    (h : prefixResourceListCheck P O ps q K = true) :
    prefixResourceBound P O ps q K := by
  intro u hu v hv hne hsig
  unfold prefixResourceListCheck at h
  have hu' : u ∈ O.take q := by simpa only [orderPrefix, List.mem_toFinset] using hu
  have hv' : v ∈ O.take q := by simpa only [orderPrefix, List.mem_toFinset] using hv
  have hpair := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h u hu') v hv')
  rcases hpair with h | h | h
  · exact False.elim (hne h)
  · exact False.elim (h hsig)
  · exact h

#print axioms prefixResourceBound_of_listCheck
end Erdos883Verified
