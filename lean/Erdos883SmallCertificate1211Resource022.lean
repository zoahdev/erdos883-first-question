import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_22 :
    (List.ofFn coreChunks1211_22).flatten =
      (coreData1211.take (coreResources1211 22).q).drop 207 := by
  decide +kernel

theorem coreCheck1211_22 :
    ∀ c : Fin 1, (coreChunks1211_22 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 22)) = true := by
  decide +kernel
#print axioms coreFlatten1211_22
#print axioms coreCheck1211_22
end Erdos883Verified
