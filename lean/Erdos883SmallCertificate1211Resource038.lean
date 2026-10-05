import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_38 :
    (List.ofFn coreChunks1211_38).flatten =
      (coreData1211.take (coreResources1211 38).q).drop 227 := by
  decide +kernel

theorem coreCheck1211_38 :
    ∀ c : Fin 1, (coreChunks1211_38 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 38)) = true := by
  decide +kernel
#print axioms coreFlatten1211_38
#print axioms coreCheck1211_38
end Erdos883Verified
