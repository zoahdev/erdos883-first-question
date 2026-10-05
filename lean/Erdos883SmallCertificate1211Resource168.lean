import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_168 :
    (List.ofFn coreChunks1211_168).flatten =
      (coreData1211.take (coreResources1211 168).q).drop 302 := by
  decide +kernel

theorem coreCheck1211_168 :
    ∀ c : Fin 1, (coreChunks1211_168 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 168)) = true := by
  decide +kernel
#print axioms coreFlatten1211_168
#print axioms coreCheck1211_168
end Erdos883Verified
