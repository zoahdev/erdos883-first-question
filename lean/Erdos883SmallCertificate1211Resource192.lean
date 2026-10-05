import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_192 :
    (List.ofFn coreChunks1211_192).flatten =
      (coreData1211.take (coreResources1211 192).q).drop 382 := by
  decide +kernel

theorem coreCheck1211_192 :
    ∀ c : Fin 1, (coreChunks1211_192 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 192)) = true := by
  decide +kernel
#print axioms coreFlatten1211_192
#print axioms coreCheck1211_192
end Erdos883Verified
