import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_62 :
    (List.ofFn coreChunks1211_62).flatten =
      (coreData1211.take (coreResources1211 62).q).drop 266 := by
  decide +kernel

theorem coreCheck1211_62 :
    ∀ c : Fin 1, (coreChunks1211_62 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 62)) = true := by
  decide +kernel
#print axioms coreFlatten1211_62
#print axioms coreCheck1211_62
end Erdos883Verified
