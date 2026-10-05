import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_15 :
    (List.ofFn coreChunks749_15).flatten =
      (coreData749.take (coreResources749 15).q).drop 137 := by
  decide +kernel

theorem coreCheck749_15 :
    ∀ c : Fin 1, (coreChunks749_15 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 15)) = true := by
  decide +kernel
#print axioms coreFlatten749_15
#print axioms coreCheck749_15
end Erdos883Verified
