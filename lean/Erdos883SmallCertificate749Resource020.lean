import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_20 :
    (List.ofFn coreChunks749_20).flatten =
      (coreData749.take (coreResources749 20).q).drop 143 := by
  decide +kernel

theorem coreCheck749_20 :
    ∀ c : Fin 1, (coreChunks749_20 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 20)) = true := by
  decide +kernel
#print axioms coreFlatten749_20
#print axioms coreCheck749_20
end Erdos883Verified
