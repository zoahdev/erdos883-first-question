import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_114 :
    (List.ofFn coreChunks749_114).flatten =
      (coreData749.take (coreResources749 114).q).drop 211 := by
  decide +kernel

theorem coreCheck749_114 :
    ∀ c : Fin 1, (coreChunks749_114 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 114)) = true := by
  decide +kernel
#print axioms coreFlatten749_114
#print axioms coreCheck749_114
end Erdos883Verified
