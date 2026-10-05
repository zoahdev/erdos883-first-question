import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_53 :
    (List.ofFn coreChunks749_53).flatten =
      (coreData749.take (coreResources749 53).q).drop 103 := by
  decide +kernel

theorem coreCheck749_53 :
    ∀ c : Fin 1, (coreChunks749_53 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 53)) = true := by
  decide +kernel
#print axioms coreFlatten749_53
#print axioms coreCheck749_53
end Erdos883Verified
