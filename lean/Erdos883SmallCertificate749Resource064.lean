import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_64 :
    (List.ofFn coreChunks749_64).flatten =
      (coreData749.take (coreResources749 64).q).drop 122 := by
  decide +kernel

theorem coreCheck749_64 :
    ∀ c : Fin 1, (coreChunks749_64 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 64)) = true := by
  decide +kernel
#print axioms coreFlatten749_64
#print axioms coreCheck749_64
end Erdos883Verified
