import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_100 :
    (List.ofFn coreChunks1211_100).flatten =
      (coreData1211.take (coreResources1211 100).q).drop 183 := by
  decide +kernel

theorem coreCheck1211_100 :
    ∀ c : Fin 1, (coreChunks1211_100 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 100)) = true := by
  decide +kernel
#print axioms coreFlatten1211_100
#print axioms coreCheck1211_100
end Erdos883Verified
