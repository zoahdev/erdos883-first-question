import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_84 :
    (List.ofFn coreChunks749_84).flatten =
      (coreData749.take (coreResources749 84).q).drop 149 := by
  decide +kernel

theorem coreCheck749_84 :
    ∀ c : Fin 1, (coreChunks749_84 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 84)) = true := by
  decide +kernel
#print axioms coreFlatten749_84
#print axioms coreCheck749_84
end Erdos883Verified
