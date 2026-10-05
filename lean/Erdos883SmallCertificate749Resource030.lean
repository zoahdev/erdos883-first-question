import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_30 :
    (List.ofFn coreChunks749_30).flatten =
      (coreData749.take (coreResources749 30).q).drop 155 := by
  decide +kernel

theorem coreCheck749_30 :
    ∀ c : Fin 1, (coreChunks749_30 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 30)) = true := by
  decide +kernel
#print axioms coreFlatten749_30
#print axioms coreCheck749_30
end Erdos883Verified
