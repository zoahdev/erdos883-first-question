import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_13 :
    (List.ofFn coreChunks749_13).flatten =
      (coreData749.take (coreResources749 13).q).drop 135 := by
  decide +kernel

theorem coreCheck749_13 :
    ∀ c : Fin 1, (coreChunks749_13 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 13)) = true := by
  decide +kernel
#print axioms coreFlatten749_13
#print axioms coreCheck749_13
end Erdos883Verified
