import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_147 :
    (List.ofFn coreChunks1211_147).flatten =
      (coreData1211.take (coreResources1211 147).q).drop 259 := by
  decide +kernel

theorem coreCheck1211_147 :
    ∀ c : Fin 1, (coreChunks1211_147 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 147)) = true := by
  decide +kernel
#print axioms coreFlatten1211_147
#print axioms coreCheck1211_147
end Erdos883Verified
