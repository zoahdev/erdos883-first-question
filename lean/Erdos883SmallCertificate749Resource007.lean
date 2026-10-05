import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_7 :
    (List.ofFn coreChunks749_7).flatten =
      (coreData749.take (coreResources749 7).q).drop 101 := by
  decide +kernel

theorem coreCheck749_7 :
    ∀ c : Fin 2, (coreChunks749_7 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 7)) = true := by
  decide +kernel
#print axioms coreFlatten749_7
#print axioms coreCheck749_7
end Erdos883Verified
