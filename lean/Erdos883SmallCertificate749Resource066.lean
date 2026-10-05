import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_66 :
    (List.ofFn coreChunks749_66).flatten =
      (coreData749.take (coreResources749 66).q).drop 124 := by
  decide +kernel

theorem coreCheck749_66 :
    ∀ c : Fin 1, (coreChunks749_66 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 66)) = true := by
  decide +kernel
#print axioms coreFlatten749_66
#print axioms coreCheck749_66
end Erdos883Verified
