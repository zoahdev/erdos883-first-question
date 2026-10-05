import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_75 :
    (List.ofFn coreChunks749_75).flatten =
      (coreData749.take (coreResources749 75).q).drop 137 := by
  decide +kernel

theorem coreCheck749_75 :
    ∀ c : Fin 1, (coreChunks749_75 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 75)) = true := by
  decide +kernel
#print axioms coreFlatten749_75
#print axioms coreCheck749_75
end Erdos883Verified
