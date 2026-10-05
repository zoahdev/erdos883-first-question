import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_28 :
    (List.ofFn coreChunks1211_28).flatten =
      (coreData1211.take (coreResources1211 28).q).drop 215 := by
  decide +kernel

theorem coreCheck1211_28 :
    ∀ c : Fin 1, (coreChunks1211_28 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 28)) = true := by
  decide +kernel
#print axioms coreFlatten1211_28
#print axioms coreCheck1211_28
end Erdos883Verified
