import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_41 :
    (List.ofFn coreChunks749_41).flatten =
      (coreData749.take (coreResources749 41).q).drop 168 := by
  decide +kernel

theorem coreCheck749_41 :
    ∀ c : Fin 1, (coreChunks749_41 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 41)) = true := by
  decide +kernel
#print axioms coreFlatten749_41
#print axioms coreCheck749_41
end Erdos883Verified
