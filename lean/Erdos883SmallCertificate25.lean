import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder25 : List ℕ := [1, 23, 19, 17, 13, 11, 7, 5, 25, 3, 9, 21, 15]
theorem smallOrder25_nodup : smallOrder25.Nodup := by decide +kernel
theorem smallOrder25_set : smallOrder25.toFinset = oddUniverse 25 := by decide +kernel

theorem finiteCheck23_25 : finiteIntervalCheck 23 25 smallOrder25 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate23_25 : ExactIntervalCertificate 23 25 smallOrder25 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck23_25
#print axioms smallOrder25_nodup
#print axioms smallOrder25_set
#print axioms finiteCheck23_25
#print axioms exactCertificate23_25
end Erdos883Verified
