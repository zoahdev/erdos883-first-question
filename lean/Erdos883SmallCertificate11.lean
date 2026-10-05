import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder11 : List ℕ := [1, 11, 7, 5, 3, 9]
theorem smallOrder11_nodup : smallOrder11.Nodup := by decide +kernel
theorem smallOrder11_set : smallOrder11.toFinset = oddUniverse 11 := by decide +kernel

theorem finiteCheck10_11 : finiteIntervalCheck 10 11 smallOrder11 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate10_11 : ExactIntervalCertificate 10 11 smallOrder11 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck10_11
#print axioms smallOrder11_nodup
#print axioms smallOrder11_set
#print axioms finiteCheck10_11
#print axioms exactCertificate10_11
end Erdos883Verified
