import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_55 :
    (List.ofFn coreChunks749_55).flatten =
      (coreData749.take (coreResources749 55).q).drop 110 := by
  decide +kernel

theorem coreCheck749_55 :
    ∀ c : Fin 1, (coreChunks749_55 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 55)) = true := by
  decide +kernel
#print axioms coreFlatten749_55
#print axioms coreCheck749_55
end Erdos883Verified
