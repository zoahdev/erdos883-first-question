import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_102 :
    (List.ofFn coreChunks749_102).flatten =
      (coreData749.take (coreResources749 102).q).drop 182 := by
  decide +kernel

theorem coreCheck749_102 :
    ∀ c : Fin 1, (coreChunks749_102 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 102)) = true := by
  decide +kernel
#print axioms coreFlatten749_102
#print axioms coreCheck749_102
end Erdos883Verified
