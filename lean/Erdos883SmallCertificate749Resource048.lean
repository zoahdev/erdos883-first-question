import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_48 :
    (List.ofFn coreChunks749_48).flatten =
      (coreData749.take (coreResources749 48).q).drop 185 := by
  decide +kernel

theorem coreCheck749_48 :
    ∀ c : Fin 1, (coreChunks749_48 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 48)) = true := by
  decide +kernel
#print axioms coreFlatten749_48
#print axioms coreCheck749_48
end Erdos883Verified
