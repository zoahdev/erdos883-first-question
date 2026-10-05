import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_16 :
    (List.ofFn coreChunks749_16).flatten =
      (coreData749.take (coreResources749 16).q).drop 138 := by
  decide +kernel

theorem coreCheck749_16 :
    ∀ c : Fin 1, (coreChunks749_16 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 16)) = true := by
  decide +kernel
#print axioms coreFlatten749_16
#print axioms coreCheck749_16
end Erdos883Verified
