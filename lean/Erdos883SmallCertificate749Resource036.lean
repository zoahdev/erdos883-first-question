import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_36 :
    (List.ofFn coreChunks749_36).flatten =
      (coreData749.take (coreResources749 36).q).drop 162 := by
  decide +kernel

theorem coreCheck749_36 :
    ∀ c : Fin 1, (coreChunks749_36 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 36)) = true := by
  decide +kernel
#print axioms coreFlatten749_36
#print axioms coreCheck749_36
end Erdos883Verified
