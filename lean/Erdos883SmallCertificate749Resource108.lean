import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_108 :
    (List.ofFn coreChunks749_108).flatten =
      (coreData749.take (coreResources749 108).q).drop 193 := by
  decide +kernel

theorem coreCheck749_108 :
    ∀ c : Fin 1, (coreChunks749_108 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 108)) = true := by
  decide +kernel
#print axioms coreFlatten749_108
#print axioms coreCheck749_108
end Erdos883Verified
