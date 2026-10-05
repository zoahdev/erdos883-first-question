import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_133 :
    (List.ofFn coreChunks749_133).flatten =
      (coreData749.take (coreResources749 133).q).drop 310 := by
  decide +kernel

theorem coreCheck749_133 :
    ∀ c : Fin 1, (coreChunks749_133 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 133)) = true := by
  decide +kernel
#print axioms coreFlatten749_133
#print axioms coreCheck749_133
end Erdos883Verified
