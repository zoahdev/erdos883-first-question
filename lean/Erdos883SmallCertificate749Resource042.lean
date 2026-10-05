import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_42 :
    (List.ofFn coreChunks749_42).flatten =
      (coreData749.take (coreResources749 42).q).drop 169 := by
  decide +kernel

theorem coreCheck749_42 :
    ∀ c : Fin 1, (coreChunks749_42 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 42)) = true := by
  decide +kernel
#print axioms coreFlatten749_42
#print axioms coreCheck749_42
end Erdos883Verified
