import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_52 :
    (List.ofFn coreChunks749_52).flatten =
      (coreData749.take (coreResources749 52).q).drop 95 := by
  decide +kernel

theorem coreCheck749_52 :
    ∀ c : Fin 1, (coreChunks749_52 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 52)) = true := by
  decide +kernel
#print axioms coreFlatten749_52
#print axioms coreCheck749_52
end Erdos883Verified
