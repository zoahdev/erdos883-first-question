import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_80 :
    (List.ofFn coreChunks749_80).flatten =
      (coreData749.take (coreResources749 80).q).drop 144 := by
  decide +kernel

theorem coreCheck749_80 :
    ∀ c : Fin 1, (coreChunks749_80 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 80)) = true := by
  decide +kernel
#print axioms coreFlatten749_80
#print axioms coreCheck749_80
end Erdos883Verified
