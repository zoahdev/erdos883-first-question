import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_17 :
    (List.ofFn coreChunks749_17).flatten =
      (coreData749.take (coreResources749 17).q).drop 139 := by
  decide +kernel

theorem coreCheck749_17 :
    ∀ c : Fin 1, (coreChunks749_17 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 17)) = true := by
  decide +kernel
#print axioms coreFlatten749_17
#print axioms coreCheck749_17
end Erdos883Verified
