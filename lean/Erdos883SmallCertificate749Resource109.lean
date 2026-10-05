import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_109 :
    (List.ofFn coreChunks749_109).flatten =
      (coreData749.take (coreResources749 109).q).drop 194 := by
  decide +kernel

theorem coreCheck749_109 :
    ∀ c : Fin 1, (coreChunks749_109 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 109)) = true := by
  decide +kernel
#print axioms coreFlatten749_109
#print axioms coreCheck749_109
end Erdos883Verified
