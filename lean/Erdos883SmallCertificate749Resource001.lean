import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_1 :
    (List.ofFn coreChunks749_1).flatten =
      (coreData749.take (coreResources749 1).q).drop 65 := by
  decide +kernel

theorem coreCheck749_1 :
    ∀ c : Fin 1, (coreChunks749_1 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 1)) = true := by
  decide +kernel
#print axioms coreFlatten749_1
#print axioms coreCheck749_1
end Erdos883Verified
