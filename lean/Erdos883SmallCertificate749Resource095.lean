import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_95 :
    (List.ofFn coreChunks749_95).flatten =
      (coreData749.take (coreResources749 95).q).drop 166 := by
  decide +kernel

theorem coreCheck749_95 :
    ∀ c : Fin 1, (coreChunks749_95 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 95)) = true := by
  decide +kernel
#print axioms coreFlatten749_95
#print axioms coreCheck749_95
end Erdos883Verified
