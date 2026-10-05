import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_122 :
    (List.ofFn coreChunks749_122).flatten =
      (coreData749.take (coreResources749 122).q).drop 235 := by
  decide +kernel

theorem coreCheck749_122 :
    ∀ c : Fin 1, (coreChunks749_122 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 122)) = true := by
  decide +kernel
#print axioms coreFlatten749_122
#print axioms coreCheck749_122
end Erdos883Verified
