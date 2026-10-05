import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_135 :
    (List.ofFn coreChunks749_135).flatten =
      (coreData749.take (coreResources749 135).q).drop 315 := by
  decide +kernel

theorem coreCheck749_135 :
    ∀ c : Fin 1, (coreChunks749_135 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 135)) = true := by
  decide +kernel
#print axioms coreFlatten749_135
#print axioms coreCheck749_135
end Erdos883Verified
