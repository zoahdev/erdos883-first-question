import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_26 :
    (List.ofFn coreChunks749_26).flatten =
      (coreData749.take (coreResources749 26).q).drop 149 := by
  decide +kernel

theorem coreCheck749_26 :
    ∀ c : Fin 1, (coreChunks749_26 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 26)) = true := by
  decide +kernel
#print axioms coreFlatten749_26
#print axioms coreCheck749_26
end Erdos883Verified
