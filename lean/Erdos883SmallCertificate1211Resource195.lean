import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_195 :
    (List.ofFn coreChunks1211_195).flatten =
      (coreData1211.take (coreResources1211 195).q).drop 403 := by
  decide +kernel

theorem coreCheck1211_195 :
    ∀ c : Fin 2, (coreChunks1211_195 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 195)) = true := by
  decide +kernel
#print axioms coreFlatten1211_195
#print axioms coreCheck1211_195
end Erdos883Verified
