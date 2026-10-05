import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_136 :
    (List.ofFn coreChunks749_136).flatten =
      (coreData749.take (coreResources749 136).q).drop 316 := by
  decide +kernel

theorem coreCheck749_136 :
    ∀ c : Fin 1, (coreChunks749_136 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 136)) = true := by
  decide +kernel
#print axioms coreFlatten749_136
#print axioms coreCheck749_136
end Erdos883Verified
