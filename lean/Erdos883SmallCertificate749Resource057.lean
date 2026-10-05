import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_57 :
    (List.ofFn coreChunks749_57).flatten =
      (coreData749.take (coreResources749 57).q).drop 114 := by
  decide +kernel

theorem coreCheck749_57 :
    ∀ c : Fin 1, (coreChunks749_57 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 57)) = true := by
  decide +kernel
#print axioms coreFlatten749_57
#print axioms coreCheck749_57
end Erdos883Verified
