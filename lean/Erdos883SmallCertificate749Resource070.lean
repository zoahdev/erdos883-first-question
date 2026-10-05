import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_70 :
    (List.ofFn coreChunks749_70).flatten =
      (coreData749.take (coreResources749 70).q).drop 131 := by
  decide +kernel

theorem coreCheck749_70 :
    ∀ c : Fin 1, (coreChunks749_70 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 70)) = true := by
  decide +kernel
#print axioms coreFlatten749_70
#print axioms coreCheck749_70
end Erdos883Verified
