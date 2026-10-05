import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_3 :
    (List.ofFn coreChunks749_3).flatten =
      (coreData749.take (coreResources749 3).q).drop 84 := by
  decide +kernel

theorem coreCheck749_3 :
    ∀ c : Fin 1, (coreChunks749_3 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 3)) = true := by
  decide +kernel
#print axioms coreFlatten749_3
#print axioms coreCheck749_3
end Erdos883Verified
