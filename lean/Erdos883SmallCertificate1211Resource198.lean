import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_198 :
    (List.ofFn coreChunks1211_198).flatten =
      (coreData1211.take (coreResources1211 198).q).drop 451 := by
  decide +kernel

theorem coreCheck1211_198 :
    ∀ c : Fin 2, (coreChunks1211_198 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 198)) = true := by
  decide +kernel
#print axioms coreFlatten1211_198
#print axioms coreCheck1211_198
end Erdos883Verified
