import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_147 :
    (List.ofFn coreChunks749_147).flatten =
      (coreData749.take (coreResources749 147).q).drop 211 := by
  decide +kernel

theorem coreCheck749_147 :
    ∀ c : Fin 1, (coreChunks749_147 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 147)) = true := by
  decide +kernel
#print axioms coreFlatten749_147
#print axioms coreCheck749_147
end Erdos883Verified
