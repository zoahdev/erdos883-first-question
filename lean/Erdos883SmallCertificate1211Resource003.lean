import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_3 :
    (List.ofFn coreChunks1211_3).flatten =
      (coreData1211.take (coreResources1211 3).q).drop 140 := by
  decide +kernel

theorem coreCheck1211_3 :
    ∀ c : Fin 1, (coreChunks1211_3 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 3)) = true := by
  decide +kernel
#print axioms coreFlatten1211_3
#print axioms coreCheck1211_3
end Erdos883Verified
