import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_39 :
    (List.ofFn coreChunks749_39).flatten =
      (coreData749.take (coreResources749 39).q).drop 166 := by
  decide +kernel

theorem coreCheck749_39 :
    ∀ c : Fin 1, (coreChunks749_39 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 39)) = true := by
  decide +kernel
#print axioms coreFlatten749_39
#print axioms coreCheck749_39
end Erdos883Verified
