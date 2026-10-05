import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_103 :
    (List.ofFn coreChunks749_103).flatten =
      (coreData749.take (coreResources749 103).q).drop 185 := by
  decide +kernel

theorem coreCheck749_103 :
    ∀ c : Fin 1, (coreChunks749_103 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 103)) = true := by
  decide +kernel
#print axioms coreFlatten749_103
#print axioms coreCheck749_103
end Erdos883Verified
