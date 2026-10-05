import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_116 :
    (List.ofFn coreChunks749_116).flatten =
      (coreData749.take (coreResources749 116).q).drop 221 := by
  decide +kernel

theorem coreCheck749_116 :
    ∀ c : Fin 1, (coreChunks749_116 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 116)) = true := by
  decide +kernel
#print axioms coreFlatten749_116
#print axioms coreCheck749_116
end Erdos883Verified
