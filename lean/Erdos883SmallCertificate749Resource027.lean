import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_27 :
    (List.ofFn coreChunks749_27).flatten =
      (coreData749.take (coreResources749 27).q).drop 150 := by
  decide +kernel

theorem coreCheck749_27 :
    ∀ c : Fin 1, (coreChunks749_27 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 27)) = true := by
  decide +kernel
#print axioms coreFlatten749_27
#print axioms coreCheck749_27
end Erdos883Verified
