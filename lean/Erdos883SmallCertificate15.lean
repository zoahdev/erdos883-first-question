import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder15 : List ℕ := [1, 13, 11, 7, 5, 3, 9, 15]
theorem smallOrder15_nodup : smallOrder15.Nodup := by decide +kernel
theorem smallOrder15_set : smallOrder15.toFinset = oddUniverse 15 := by decide +kernel

theorem finiteCheck14_15 : finiteIntervalCheck 14 15 smallOrder15 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate14_15 : ExactIntervalCertificate 14 15 smallOrder15 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck14_15
#print axioms smallOrder15_nodup
#print axioms smallOrder15_set
#print axioms finiteCheck14_15
#print axioms exactCertificate14_15
end Erdos883Verified
