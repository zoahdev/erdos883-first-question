import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_61 :
    (List.ofFn coreChunks749_61).flatten =
      (coreData749.take (coreResources749 61).q).drop 119 := by
  decide +kernel

theorem coreCheck749_61 :
    ∀ c : Fin 1, (coreChunks749_61 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 61)) = true := by
  decide +kernel
#print axioms coreFlatten749_61
#print axioms coreCheck749_61
end Erdos883Verified
