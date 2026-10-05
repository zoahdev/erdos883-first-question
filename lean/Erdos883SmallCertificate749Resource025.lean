import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_25 :
    (List.ofFn coreChunks749_25).flatten =
      (coreData749.take (coreResources749 25).q).drop 148 := by
  decide +kernel

theorem coreCheck749_25 :
    ∀ c : Fin 1, (coreChunks749_25 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 25)) = true := by
  decide +kernel
#print axioms coreFlatten749_25
#print axioms coreCheck749_25
end Erdos883Verified
