import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_71 :
    (List.ofFn coreChunks1211_71).flatten =
      (coreData1211.take (coreResources1211 71).q).drop 277 := by
  decide +kernel

theorem coreCheck1211_71 :
    ∀ c : Fin 1, (coreChunks1211_71 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 71)) = true := by
  decide +kernel
#print axioms coreFlatten1211_71
#print axioms coreCheck1211_71
end Erdos883Verified
