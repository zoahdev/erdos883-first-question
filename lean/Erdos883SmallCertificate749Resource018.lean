import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_18 :
    (List.ofFn coreChunks749_18).flatten =
      (coreData749.take (coreResources749 18).q).drop 140 := by
  decide +kernel

theorem coreCheck749_18 :
    ∀ c : Fin 1, (coreChunks749_18 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 18)) = true := by
  decide +kernel
#print axioms coreFlatten749_18
#print axioms coreCheck749_18
end Erdos883Verified
