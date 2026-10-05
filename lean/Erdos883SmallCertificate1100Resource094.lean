import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_94 :
    (List.ofFn coreChunks1100_94).flatten =
      (coreData1100.take (coreResources1100 94).q).drop 185 := by
  decide +kernel

theorem coreCheck1100_94 :
    ∀ c : Fin 1, (coreChunks1100_94 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 94)) = true := by
  decide +kernel
#print axioms coreFlatten1100_94
#print axioms coreCheck1100_94
end Erdos883Verified
