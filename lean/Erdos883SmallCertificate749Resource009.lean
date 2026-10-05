import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_9 :
    (List.ofFn coreChunks749_9).flatten =
      (coreData749.take (coreResources749 9).q).drop 130 := by
  decide +kernel

theorem coreCheck749_9 :
    ∀ c : Fin 1, (coreChunks749_9 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 9)) = true := by
  decide +kernel
#print axioms coreFlatten749_9
#print axioms coreCheck749_9
end Erdos883Verified
