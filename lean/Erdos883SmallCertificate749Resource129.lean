import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_129 :
    (List.ofFn coreChunks749_129).flatten =
      (coreData749.take (coreResources749 129).q).drop 298 := by
  decide +kernel

theorem coreCheck749_129 :
    ∀ c : Fin 1, (coreChunks749_129 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 129)) = true := by
  decide +kernel
#print axioms coreFlatten749_129
#print axioms coreCheck749_129
end Erdos883Verified
