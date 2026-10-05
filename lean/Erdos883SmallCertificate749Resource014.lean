import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_14 :
    (List.ofFn coreChunks749_14).flatten =
      (coreData749.take (coreResources749 14).q).drop 136 := by
  decide +kernel

theorem coreCheck749_14 :
    ∀ c : Fin 1, (coreChunks749_14 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 14)) = true := by
  decide +kernel
#print axioms coreFlatten749_14
#print axioms coreCheck749_14
end Erdos883Verified
