import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_19 :
    (List.ofFn coreChunks749_19).flatten =
      (coreData749.take (coreResources749 19).q).drop 141 := by
  decide +kernel

theorem coreCheck749_19 :
    ∀ c : Fin 1, (coreChunks749_19 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 19)) = true := by
  decide +kernel
#print axioms coreFlatten749_19
#print axioms coreCheck749_19
end Erdos883Verified
