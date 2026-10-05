import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_119 :
    (List.ofFn coreChunks749_119).flatten =
      (coreData749.take (coreResources749 119).q).drop 227 := by
  decide +kernel

theorem coreCheck749_119 :
    ∀ c : Fin 1, (coreChunks749_119 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 119)) = true := by
  decide +kernel
#print axioms coreFlatten749_119
#print axioms coreCheck749_119
end Erdos883Verified
