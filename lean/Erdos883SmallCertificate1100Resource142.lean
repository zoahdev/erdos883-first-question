import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_142 :
    (List.ofFn coreChunks1100_142).flatten =
      (coreData1100.take (coreResources1100 142).q).drop 268 := by
  decide +kernel

theorem coreCheck1100_142 :
    ∀ c : Fin 1, (coreChunks1100_142 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 142)) = true := by
  decide +kernel
#print axioms coreFlatten1100_142
#print axioms coreCheck1100_142
end Erdos883Verified
