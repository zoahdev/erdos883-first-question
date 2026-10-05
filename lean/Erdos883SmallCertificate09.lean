import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder09 : List ℕ := [1, 7, 5, 3, 9]
theorem smallOrder09_nodup : smallOrder09.Nodup := by decide +kernel
theorem smallOrder09_set : smallOrder09.toFinset = oddUniverse 9 := by decide +kernel

theorem finiteCheck08_09 : finiteIntervalCheck 8 9 smallOrder09 [3, 5, 7, 11] := by
  unfold finiteIntervalCheck intervalWitness
  decide +kernel

theorem exactCertificate08_09 : ExactIntervalCertificate 8 9 smallOrder09 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck08_09
#print axioms smallOrder09_nodup
#print axioms smallOrder09_set
#print axioms finiteCheck08_09
#print axioms exactCertificate08_09
end Erdos883Verified
