import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_74 :
    (List.ofFn coreChunks749_74).flatten =
      (coreData749.take (coreResources749 74).q).drop 136 := by
  decide +kernel

theorem coreCheck749_74 :
    ∀ c : Fin 1, (coreChunks749_74 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 74)) = true := by
  decide +kernel
#print axioms coreFlatten749_74
#print axioms coreCheck749_74
end Erdos883Verified
