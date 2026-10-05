import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_56 :
    (List.ofFn coreChunks749_56).flatten =
      (coreData749.take (coreResources749 56).q).drop 111 := by
  decide +kernel

theorem coreCheck749_56 :
    ∀ c : Fin 1, (coreChunks749_56 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 56)) = true := by
  decide +kernel
#print axioms coreFlatten749_56
#print axioms coreCheck749_56
end Erdos883Verified
