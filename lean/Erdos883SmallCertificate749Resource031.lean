import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_31 :
    (List.ofFn coreChunks749_31).flatten =
      (coreData749.take (coreResources749 31).q).drop 157 := by
  decide +kernel

theorem coreCheck749_31 :
    ∀ c : Fin 1, (coreChunks749_31 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 31)) = true := by
  decide +kernel
#print axioms coreFlatten749_31
#print axioms coreCheck749_31
end Erdos883Verified
