import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_32 :
    (List.ofFn coreChunks1211_32).flatten =
      (coreData1211.take (coreResources1211 32).q).drop 221 := by
  decide +kernel

theorem coreCheck1211_32 :
    ∀ c : Fin 1, (coreChunks1211_32 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 32)) = true := by
  decide +kernel
#print axioms coreFlatten1211_32
#print axioms coreCheck1211_32
end Erdos883Verified
