import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_34 :
    (List.ofFn coreChunks1211_34).flatten =
      (coreData1211.take (coreResources1211 34).q).drop 223 := by
  decide +kernel

theorem coreCheck1211_34 :
    ∀ c : Fin 1, (coreChunks1211_34 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 34)) = true := by
  decide +kernel
#print axioms coreFlatten1211_34
#print axioms coreCheck1211_34
end Erdos883Verified
