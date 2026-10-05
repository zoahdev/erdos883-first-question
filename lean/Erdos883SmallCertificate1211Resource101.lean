import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_101 :
    (List.ofFn coreChunks1211_101).flatten =
      (coreData1211.take (coreResources1211 101).q).drop 184 := by
  decide +kernel

theorem coreCheck1211_101 :
    ∀ c : Fin 1, (coreChunks1211_101 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 101)) = true := by
  decide +kernel
#print axioms coreFlatten1211_101
#print axioms coreCheck1211_101
end Erdos883Verified
