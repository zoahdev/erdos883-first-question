import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_222 :
    (List.ofFn coreChunks1211_222).flatten =
      (coreData1211.take (coreResources1211 222).q).drop 395 := by
  decide +kernel

theorem coreCheck1211_222 :
    ∀ c : Fin 1, (coreChunks1211_222 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 222)) = true := by
  decide +kernel
#print axioms coreFlatten1211_222
#print axioms coreCheck1211_222
end Erdos883Verified
