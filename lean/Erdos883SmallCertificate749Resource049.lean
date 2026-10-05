import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_49 :
    (List.ofFn coreChunks749_49).flatten =
      (coreData749.take (coreResources749 49).q).drop 186 := by
  decide +kernel

theorem coreCheck749_49 :
    ∀ c : Fin 1, (coreChunks749_49 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 49)) = true := by
  decide +kernel
#print axioms coreFlatten749_49
#print axioms coreCheck749_49
end Erdos883Verified
