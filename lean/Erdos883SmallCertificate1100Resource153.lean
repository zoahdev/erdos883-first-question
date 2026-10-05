import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_153 :
    (List.ofFn coreChunks1100_153).flatten =
      (coreData1100.take (coreResources1100 153).q).drop 288 := by
  decide +kernel

theorem coreCheck1100_153 :
    ∀ c : Fin 1, (coreChunks1100_153 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 153)) = true := by
  decide +kernel
#print axioms coreFlatten1100_153
#print axioms coreCheck1100_153
end Erdos883Verified
