import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_123 :
    (List.ofFn coreChunks749_123).flatten =
      (coreData749.take (coreResources749 123).q).drop 237 := by
  decide +kernel

theorem coreCheck749_123 :
    ∀ c : Fin 1, (coreChunks749_123 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 123)) = true := by
  decide +kernel
#print axioms coreFlatten749_123
#print axioms coreCheck749_123
end Erdos883Verified
