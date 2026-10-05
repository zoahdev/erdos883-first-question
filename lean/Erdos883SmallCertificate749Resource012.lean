import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_12 :
    (List.ofFn coreChunks749_12).flatten =
      (coreData749.take (coreResources749 12).q).drop 134 := by
  decide +kernel

theorem coreCheck749_12 :
    ∀ c : Fin 1, (coreChunks749_12 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 12)) = true := by
  decide +kernel
#print axioms coreFlatten749_12
#print axioms coreCheck749_12
end Erdos883Verified
