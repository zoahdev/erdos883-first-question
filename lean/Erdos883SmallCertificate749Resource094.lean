import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_94 :
    (List.ofFn coreChunks749_94).flatten =
      (coreData749.take (coreResources749 94).q).drop 165 := by
  decide +kernel

theorem coreCheck749_94 :
    ∀ c : Fin 1, (coreChunks749_94 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 94)) = true := by
  decide +kernel
#print axioms coreFlatten749_94
#print axioms coreCheck749_94
end Erdos883Verified
