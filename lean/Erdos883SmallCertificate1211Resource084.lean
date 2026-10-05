import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_84 :
    (List.ofFn coreChunks1211_84).flatten =
      (coreData1211.take (coreResources1211 84).q).drop 140 := by
  decide +kernel

theorem coreCheck1211_84 :
    ∀ c : Fin 1, (coreChunks1211_84 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 84)) = true := by
  decide +kernel
#print axioms coreFlatten1211_84
#print axioms coreCheck1211_84
end Erdos883Verified
