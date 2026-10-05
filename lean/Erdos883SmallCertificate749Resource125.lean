import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_125 :
    (List.ofFn coreChunks749_125).flatten =
      (coreData749.take (coreResources749 125).q).drop 246 := by
  decide +kernel

theorem coreCheck749_125 :
    ∀ c : Fin 1, (coreChunks749_125 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 125)) = true := by
  decide +kernel
#print axioms coreFlatten749_125
#print axioms coreCheck749_125
end Erdos883Verified
