import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder13 : List ℕ := [1, 13, 11, 7, 5, 3, 9]
theorem smallOrder13_nodup : smallOrder13.Nodup := by decide +kernel
theorem smallOrder13_set : smallOrder13.toFinset = oddUniverse 13 := by decide +kernel

theorem finiteCheck12_13 : finiteIntervalCheck 12 13 smallOrder13 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate12_13 : ExactIntervalCertificate 12 13 smallOrder13 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck12_13
#print axioms smallOrder13_nodup
#print axioms smallOrder13_set
#print axioms finiteCheck12_13
#print axioms exactCertificate12_13
end Erdos883Verified
