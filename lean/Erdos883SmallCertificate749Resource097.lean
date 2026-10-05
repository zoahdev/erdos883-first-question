import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_97 :
    (List.ofFn coreChunks749_97).flatten =
      (coreData749.take (coreResources749 97).q).drop 168 := by
  decide +kernel

theorem coreCheck749_97 :
    ∀ c : Fin 1, (coreChunks749_97 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 97)) = true := by
  decide +kernel
#print axioms coreFlatten749_97
#print axioms coreCheck749_97
end Erdos883Verified
