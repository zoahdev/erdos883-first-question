import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_138 :
    (List.ofFn coreChunks1211_138).flatten =
      (coreData1211.take (coreResources1211 138).q).drop 240 := by
  decide +kernel

theorem coreCheck1211_138 :
    ∀ c : Fin 1, (coreChunks1211_138 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 138)) = true := by
  decide +kernel
#print axioms coreFlatten1211_138
#print axioms coreCheck1211_138
end Erdos883Verified
