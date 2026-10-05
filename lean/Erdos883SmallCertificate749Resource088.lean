import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_88 :
    (List.ofFn coreChunks749_88).flatten =
      (coreData749.take (coreResources749 88).q).drop 155 := by
  decide +kernel

theorem coreCheck749_88 :
    ∀ c : Fin 1, (coreChunks749_88 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 88)) = true := by
  decide +kernel
#print axioms coreFlatten749_88
#print axioms coreCheck749_88
end Erdos883Verified
