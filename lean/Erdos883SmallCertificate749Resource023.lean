import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_23 :
    (List.ofFn coreChunks749_23).flatten =
      (coreData749.take (coreResources749 23).q).drop 146 := by
  decide +kernel

theorem coreCheck749_23 :
    ∀ c : Fin 1, (coreChunks749_23 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 23)) = true := by
  decide +kernel
#print axioms coreFlatten749_23
#print axioms coreCheck749_23
end Erdos883Verified
