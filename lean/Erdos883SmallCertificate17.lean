import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder17 : List ℕ := [1, 17, 13, 11, 7, 5, 3, 9, 15]
theorem smallOrder17_nodup : smallOrder17.Nodup := by decide +kernel
theorem smallOrder17_set : smallOrder17.toFinset = oddUniverse 17 := by decide +kernel

theorem finiteCheck16_17 : finiteIntervalCheck 16 17 smallOrder17 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate16_17 : ExactIntervalCertificate 16 17 smallOrder17 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck16_17
#print axioms smallOrder17_nodup
#print axioms smallOrder17_set
#print axioms finiteCheck16_17
#print axioms exactCertificate16_17
end Erdos883Verified
