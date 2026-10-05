import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_113 :
    (List.ofFn coreChunks749_113).flatten =
      (coreData749.take (coreResources749 113).q).drop 205 := by
  decide +kernel

theorem coreCheck749_113 :
    ∀ c : Fin 1, (coreChunks749_113 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 113)) = true := by
  decide +kernel
#print axioms coreFlatten749_113
#print axioms coreCheck749_113
end Erdos883Verified
