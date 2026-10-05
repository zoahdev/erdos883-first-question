import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_37 :
    (List.ofFn coreChunks1211_37).flatten =
      (coreData1211.take (coreResources1211 37).q).drop 226 := by
  decide +kernel

theorem coreCheck1211_37 :
    ∀ c : Fin 1, (coreChunks1211_37 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 37)) = true := by
  decide +kernel
#print axioms coreFlatten1211_37
#print axioms coreCheck1211_37
end Erdos883Verified
