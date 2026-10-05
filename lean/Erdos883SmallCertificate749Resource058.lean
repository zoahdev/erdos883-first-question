import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_58 :
    (List.ofFn coreChunks749_58).flatten =
      (coreData749.take (coreResources749 58).q).drop 115 := by
  decide +kernel

theorem coreCheck749_58 :
    ∀ c : Fin 1, (coreChunks749_58 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 58)) = true := by
  decide +kernel
#print axioms coreFlatten749_58
#print axioms coreCheck749_58
end Erdos883Verified
