import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_81 :
    (List.ofFn coreChunks749_81).flatten =
      (coreData749.take (coreResources749 81).q).drop 145 := by
  decide +kernel

theorem coreCheck749_81 :
    ∀ c : Fin 1, (coreChunks749_81 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 81)) = true := by
  decide +kernel
#print axioms coreFlatten749_81
#print axioms coreCheck749_81
end Erdos883Verified
