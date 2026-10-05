import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_11 :
    (List.ofFn coreChunks749_11).flatten =
      (coreData749.take (coreResources749 11).q).drop 132 := by
  decide +kernel

theorem coreCheck749_11 :
    ∀ c : Fin 1, (coreChunks749_11 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 11)) = true := by
  decide +kernel
#print axioms coreFlatten749_11
#print axioms coreCheck749_11
end Erdos883Verified
