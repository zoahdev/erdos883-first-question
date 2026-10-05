import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Erdos883Verified

def smallOrder07 : List ℕ := [1, 7, 5, 3]
theorem smallOrder07_nodup : smallOrder07.Nodup := by decide +kernel
theorem smallOrder07_set : smallOrder07.toFinset = oddUniverse 7 := by decide +kernel

theorem finiteCheck06_07 : finiteIntervalCheck 6 7 smallOrder07 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate06_07 : ExactIntervalCertificate 6 7 smallOrder07 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck06_07
#print axioms smallOrder07_nodup
#print axioms smallOrder07_set
#print axioms finiteCheck06_07
#print axioms exactCertificate06_07
end Erdos883Verified
