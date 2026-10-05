import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_24 :
    (List.ofFn coreChunks749_24).flatten =
      (coreData749.take (coreResources749 24).q).drop 147 := by
  decide +kernel

theorem coreCheck749_24 :
    ∀ c : Fin 1, (coreChunks749_24 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 24)) = true := by
  decide +kernel
#print axioms coreFlatten749_24
#print axioms coreCheck749_24
end Erdos883Verified
