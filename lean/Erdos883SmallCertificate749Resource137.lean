import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_137 :
    (List.ofFn coreChunks749_137).flatten =
      (coreData749.take (coreResources749 137).q).drop 319 := by
  decide +kernel

theorem coreCheck749_137 :
    ∀ c : Fin 1, (coreChunks749_137 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 137)) = true := by
  decide +kernel
#print axioms coreFlatten749_137
#print axioms coreCheck749_137
end Erdos883Verified
