import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_118 :
    (List.ofFn coreChunks749_118).flatten =
      (coreData749.take (coreResources749 118).q).drop 225 := by
  decide +kernel

theorem coreCheck749_118 :
    ∀ c : Fin 1, (coreChunks749_118 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 118)) = true := by
  decide +kernel
#print axioms coreFlatten749_118
#print axioms coreCheck749_118
end Erdos883Verified
