import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_73 :
    (List.ofFn coreChunks749_73).flatten =
      (coreData749.take (coreResources749 73).q).drop 135 := by
  decide +kernel

theorem coreCheck749_73 :
    ∀ c : Fin 1, (coreChunks749_73 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 73)) = true := by
  decide +kernel
#print axioms coreFlatten749_73
#print axioms coreCheck749_73
end Erdos883Verified
