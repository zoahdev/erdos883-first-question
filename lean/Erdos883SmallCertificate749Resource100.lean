import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_100 :
    (List.ofFn coreChunks749_100).flatten =
      (coreData749.take (coreResources749 100).q).drop 173 := by
  decide +kernel

theorem coreCheck749_100 :
    ∀ c : Fin 1, (coreChunks749_100 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 100)) = true := by
  decide +kernel
#print axioms coreFlatten749_100
#print axioms coreCheck749_100
end Erdos883Verified
