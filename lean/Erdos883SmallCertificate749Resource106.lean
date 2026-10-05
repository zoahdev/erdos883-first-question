import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_106 :
    (List.ofFn coreChunks749_106).flatten =
      (coreData749.take (coreResources749 106).q).drop 190 := by
  decide +kernel

theorem coreCheck749_106 :
    ∀ c : Fin 1, (coreChunks749_106 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 106)) = true := by
  decide +kernel
#print axioms coreFlatten749_106
#print axioms coreCheck749_106
end Erdos883Verified
