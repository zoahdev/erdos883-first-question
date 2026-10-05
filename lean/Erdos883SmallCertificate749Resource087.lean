import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_87 :
    (List.ofFn coreChunks749_87).flatten =
      (coreData749.take (coreResources749 87).q).drop 154 := by
  decide +kernel

theorem coreCheck749_87 :
    ∀ c : Fin 1, (coreChunks749_87 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 87)) = true := by
  decide +kernel
#print axioms coreFlatten749_87
#print axioms coreCheck749_87
end Erdos883Verified
