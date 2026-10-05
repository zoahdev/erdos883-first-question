import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_10 :
    (List.ofFn coreChunks1211_10).flatten =
      (coreData1211.take (coreResources1211 10).q).drop 162 := by
  decide +kernel

theorem coreCheck1211_10 :
    ∀ c : Fin 2, (coreChunks1211_10 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 10)) = true := by
  decide +kernel
#print axioms coreFlatten1211_10
#print axioms coreCheck1211_10
end Erdos883Verified
