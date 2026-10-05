import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_10 :
    (List.ofFn coreChunks749_10).flatten =
      (coreData749.take (coreResources749 10).q).drop 131 := by
  decide +kernel

theorem coreCheck749_10 :
    ∀ c : Fin 1, (coreChunks749_10 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 10)) = true := by
  decide +kernel
#print axioms coreFlatten749_10
#print axioms coreCheck749_10
end Erdos883Verified
