import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_131 :
    (List.ofFn coreChunks749_131).flatten =
      (coreData749.take (coreResources749 131).q).drop 304 := by
  decide +kernel

theorem coreCheck749_131 :
    ∀ c : Fin 1, (coreChunks749_131 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 131)) = true := by
  decide +kernel
#print axioms coreFlatten749_131
#print axioms coreCheck749_131
end Erdos883Verified
