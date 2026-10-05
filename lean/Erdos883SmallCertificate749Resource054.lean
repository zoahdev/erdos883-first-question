import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_54 :
    (List.ofFn coreChunks749_54).flatten =
      (coreData749.take (coreResources749 54).q).drop 104 := by
  decide +kernel

theorem coreCheck749_54 :
    ∀ c : Fin 1, (coreChunks749_54 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 54)) = true := by
  decide +kernel
#print axioms coreFlatten749_54
#print axioms coreCheck749_54
end Erdos883Verified
