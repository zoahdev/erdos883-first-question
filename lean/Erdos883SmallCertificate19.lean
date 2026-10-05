import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder19 : List ℕ := [1, 19, 17, 13, 11, 7, 5, 3, 9, 15]
theorem smallOrder19_nodup : smallOrder19.Nodup := by decide +kernel
theorem smallOrder19_set : smallOrder19.toFinset = oddUniverse 19 := by decide +kernel

theorem finiteCheck18_19 : finiteIntervalCheck 18 19 smallOrder19 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate18_19 : ExactIntervalCertificate 18 19 smallOrder19 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck18_19
#print axioms smallOrder19_nodup
#print axioms smallOrder19_set
#print axioms finiteCheck18_19
#print axioms exactCertificate18_19
end Erdos883Verified
