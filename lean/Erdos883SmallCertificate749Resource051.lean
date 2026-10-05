import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_51 :
    (List.ofFn coreChunks749_51).flatten =
      (coreData749.take (coreResources749 51).q).drop 94 := by
  decide +kernel

theorem coreCheck749_51 :
    ∀ c : Fin 1, (coreChunks749_51 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 51)) = true := by
  decide +kernel
#print axioms coreFlatten749_51
#print axioms coreCheck749_51
end Erdos883Verified
