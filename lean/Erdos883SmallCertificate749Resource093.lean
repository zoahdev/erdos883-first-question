import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_93 :
    (List.ofFn coreChunks749_93).flatten =
      (coreData749.take (coreResources749 93).q).drop 163 := by
  decide +kernel

theorem coreCheck749_93 :
    ∀ c : Fin 1, (coreChunks749_93 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 93)) = true := by
  decide +kernel
#print axioms coreFlatten749_93
#print axioms coreCheck749_93
end Erdos883Verified
