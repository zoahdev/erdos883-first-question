import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_22 :
    (List.ofFn coreChunks749_22).flatten =
      (coreData749.take (coreResources749 22).q).drop 145 := by
  decide +kernel

theorem coreCheck749_22 :
    ∀ c : Fin 1, (coreChunks749_22 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 22)) = true := by
  decide +kernel
#print axioms coreFlatten749_22
#print axioms coreCheck749_22
end Erdos883Verified
