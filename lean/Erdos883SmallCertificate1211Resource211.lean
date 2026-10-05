import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_211 :
    (List.ofFn coreChunks1211_211).flatten =
      (coreData1211.take (coreResources1211 211).q).drop 530 := by
  decide +kernel

theorem coreCheck1211_211 :
    ∀ c : Fin 1, (coreChunks1211_211 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 211)) = true := by
  decide +kernel
#print axioms coreFlatten1211_211
#print axioms coreCheck1211_211
end Erdos883Verified
