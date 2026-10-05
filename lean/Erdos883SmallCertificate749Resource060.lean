import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_60 :
    (List.ofFn coreChunks749_60).flatten =
      (coreData749.take (coreResources749 60).q).drop 118 := by
  decide +kernel

theorem coreCheck749_60 :
    ∀ c : Fin 1, (coreChunks749_60 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 60)) = true := by
  decide +kernel
#print axioms coreFlatten749_60
#print axioms coreCheck749_60
end Erdos883Verified
