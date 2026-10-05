import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_97 :
    (List.ofFn coreChunks1211_97).flatten =
      (coreData1211.take (coreResources1211 97).q).drop 180 := by
  decide +kernel

theorem coreCheck1211_97 :
    ∀ c : Fin 1, (coreChunks1211_97 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 97)) = true := by
  decide +kernel
#print axioms coreFlatten1211_97
#print axioms coreCheck1211_97
end Erdos883Verified
