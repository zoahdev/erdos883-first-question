import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_120 :
    (List.ofFn coreChunks749_120).flatten =
      (coreData749.take (coreResources749 120).q).drop 231 := by
  decide +kernel

theorem coreCheck749_120 :
    ∀ c : Fin 1, (coreChunks749_120 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 120)) = true := by
  decide +kernel
#print axioms coreFlatten749_120
#print axioms coreCheck749_120
end Erdos883Verified
