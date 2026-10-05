import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_79 :
    (List.ofFn coreChunks749_79).flatten =
      (coreData749.take (coreResources749 79).q).drop 141 := by
  decide +kernel

theorem coreCheck749_79 :
    ∀ c : Fin 1, (coreChunks749_79 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 79)) = true := by
  decide +kernel
#print axioms coreFlatten749_79
#print axioms coreCheck749_79
end Erdos883Verified
