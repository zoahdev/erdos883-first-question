import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_83 :
    (List.ofFn coreChunks749_83).flatten =
      (coreData749.take (coreResources749 83).q).drop 148 := by
  decide +kernel

theorem coreCheck749_83 :
    ∀ c : Fin 1, (coreChunks749_83 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 83)) = true := by
  decide +kernel
#print axioms coreFlatten749_83
#print axioms coreCheck749_83
end Erdos883Verified
