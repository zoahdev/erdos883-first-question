import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_4 :
    (List.ofFn coreChunks749_4).flatten =
      (coreData749.take (coreResources749 4).q).drop 85 := by
  decide +kernel

theorem coreCheck749_4 :
    ∀ c : Fin 1, (coreChunks749_4 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 4)) = true := by
  decide +kernel
#print axioms coreFlatten749_4
#print axioms coreCheck749_4
end Erdos883Verified
