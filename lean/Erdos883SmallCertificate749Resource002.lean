import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_2 :
    (List.ofFn coreChunks749_2).flatten =
      (coreData749.take (coreResources749 2).q).drop 66 := by
  decide +kernel

theorem coreCheck749_2 :
    ∀ c : Fin 2, (coreChunks749_2 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 2)) = true := by
  decide +kernel
#print axioms coreFlatten749_2
#print axioms coreCheck749_2
end Erdos883Verified
