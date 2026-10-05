import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_82 :
    (List.ofFn coreChunks749_82).flatten =
      (coreData749.take (coreResources749 82).q).drop 146 := by
  decide +kernel

theorem coreCheck749_82 :
    ∀ c : Fin 1, (coreChunks749_82 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 82)) = true := by
  decide +kernel
#print axioms coreFlatten749_82
#print axioms coreCheck749_82
end Erdos883Verified
