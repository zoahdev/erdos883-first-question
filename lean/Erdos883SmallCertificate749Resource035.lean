import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_35 :
    (List.ofFn coreChunks749_35).flatten =
      (coreData749.take (coreResources749 35).q).drop 161 := by
  decide +kernel

theorem coreCheck749_35 :
    ∀ c : Fin 1, (coreChunks749_35 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 35)) = true := by
  decide +kernel
#print axioms coreFlatten749_35
#print axioms coreCheck749_35
end Erdos883Verified
