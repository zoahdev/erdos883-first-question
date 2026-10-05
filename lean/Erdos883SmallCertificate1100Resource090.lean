import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_90 :
    (List.ofFn coreChunks1100_90).flatten =
      (coreData1100.take (coreResources1100 90).q).drop 178 := by
  decide +kernel

theorem coreCheck1100_90 :
    ∀ c : Fin 1, (coreChunks1100_90 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 90)) = true := by
  decide +kernel
#print axioms coreFlatten1100_90
#print axioms coreCheck1100_90
end Erdos883Verified
