import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_117 :
    (List.ofFn coreChunks749_117).flatten =
      (coreData749.take (coreResources749 117).q).drop 224 := by
  decide +kernel

theorem coreCheck749_117 :
    ∀ c : Fin 1, (coreChunks749_117 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 117)) = true := by
  decide +kernel
#print axioms coreFlatten749_117
#print axioms coreCheck749_117
end Erdos883Verified
