import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_28 :
    (List.ofFn coreChunks749_28).flatten =
      (coreData749.take (coreResources749 28).q).drop 151 := by
  decide +kernel

theorem coreCheck749_28 :
    ∀ c : Fin 1, (coreChunks749_28 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 28)) = true := by
  decide +kernel
#print axioms coreFlatten749_28
#print axioms coreCheck749_28
end Erdos883Verified
