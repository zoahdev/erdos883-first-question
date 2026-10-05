import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_78 :
    (List.ofFn coreChunks1100_78).flatten =
      (coreData1100.take (coreResources1100 78).q).drop 163 := by
  decide +kernel

theorem coreCheck1100_78 :
    ∀ c : Fin 1, (coreChunks1100_78 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 78)) = true := by
  decide +kernel
#print axioms coreFlatten1100_78
#print axioms coreCheck1100_78
end Erdos883Verified
