import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_124 :
    (List.ofFn coreChunks749_124).flatten =
      (coreData749.take (coreResources749 124).q).drop 245 := by
  decide +kernel

theorem coreCheck749_124 :
    ∀ c : Fin 1, (coreChunks749_124 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 124)) = true := by
  decide +kernel
#print axioms coreFlatten749_124
#print axioms coreCheck749_124
end Erdos883Verified
