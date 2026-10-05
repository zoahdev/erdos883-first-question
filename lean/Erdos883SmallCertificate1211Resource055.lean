import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_55 :
    (List.ofFn coreChunks1211_55).flatten =
      (coreData1211.take (coreResources1211 55).q).drop 256 := by
  decide +kernel

theorem coreCheck1211_55 :
    ∀ c : Fin 1, (coreChunks1211_55 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 55)) = true := by
  decide +kernel
#print axioms coreFlatten1211_55
#print axioms coreCheck1211_55
end Erdos883Verified
