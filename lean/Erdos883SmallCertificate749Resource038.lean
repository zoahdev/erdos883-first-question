import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_38 :
    (List.ofFn coreChunks749_38).flatten =
      (coreData749.take (coreResources749 38).q).drop 165 := by
  decide +kernel

theorem coreCheck749_38 :
    ∀ c : Fin 1, (coreChunks749_38 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 38)) = true := by
  decide +kernel
#print axioms coreFlatten749_38
#print axioms coreCheck749_38
end Erdos883Verified
