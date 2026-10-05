import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_127 :
    (List.ofFn coreChunks749_127).flatten =
      (coreData749.take (coreResources749 127).q).drop 266 := by
  decide +kernel

theorem coreCheck749_127 :
    ∀ c : Fin 1, (coreChunks749_127 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 127)) = true := by
  decide +kernel
#print axioms coreFlatten749_127
#print axioms coreCheck749_127
end Erdos883Verified
