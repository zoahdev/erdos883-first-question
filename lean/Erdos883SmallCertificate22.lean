import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder22 : List ℕ := [1, 19, 17, 13, 11, 7, 5, 3, 9, 21, 15]
theorem smallOrder22_nodup : smallOrder22.Nodup := by decide +kernel
theorem smallOrder22_set : smallOrder22.toFinset = oddUniverse 22 := by decide +kernel

theorem finiteCheck20_22 : finiteIntervalCheck 20 22 smallOrder22 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate20_22 : ExactIntervalCertificate 20 22 smallOrder22 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck20_22
#print axioms smallOrder22_nodup
#print axioms smallOrder22_set
#print axioms finiteCheck20_22
#print axioms exactCertificate20_22
end Erdos883Verified
