import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_204 :
    (List.ofFn coreChunks1211_204).flatten =
      (coreData1211.take (coreResources1211 204).q).drop 499 := by
  decide +kernel

theorem coreCheck1211_204 :
    ∀ c : Fin 1, (coreChunks1211_204 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 204)) = true := by
  decide +kernel
#print axioms coreFlatten1211_204
#print axioms coreCheck1211_204
end Erdos883Verified
