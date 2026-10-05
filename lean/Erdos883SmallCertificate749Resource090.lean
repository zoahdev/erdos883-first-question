import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_90 :
    (List.ofFn coreChunks749_90).flatten =
      (coreData749.take (coreResources749 90).q).drop 160 := by
  decide +kernel

theorem coreCheck749_90 :
    ∀ c : Fin 1, (coreChunks749_90 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 90)) = true := by
  decide +kernel
#print axioms coreFlatten749_90
#print axioms coreCheck749_90
end Erdos883Verified
