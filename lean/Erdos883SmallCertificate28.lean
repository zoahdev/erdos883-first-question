import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder28 : List ℕ := [1, 23, 19, 17, 13, 11, 7, 5, 25, 3, 9, 27, 21, 15]
theorem smallOrder28_nodup : smallOrder28.Nodup := by decide +kernel
theorem smallOrder28_set : smallOrder28.toFinset = oddUniverse 28 := by decide +kernel

theorem finiteCheck26_28 : finiteIntervalCheck 26 28 smallOrder28 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate26_28 : ExactIntervalCertificate 26 28 smallOrder28 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck26_28
#print axioms smallOrder28_nodup
#print axioms smallOrder28_set
#print axioms finiteCheck26_28
#print axioms exactCertificate26_28
end Erdos883Verified
