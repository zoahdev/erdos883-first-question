import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_78 :
    (List.ofFn coreChunks749_78).flatten =
      (coreData749.take (coreResources749 78).q).drop 140 := by
  decide +kernel

theorem coreCheck749_78 :
    ∀ c : Fin 1, (coreChunks749_78 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 78)) = true := by
  decide +kernel
#print axioms coreFlatten749_78
#print axioms coreCheck749_78
end Erdos883Verified
