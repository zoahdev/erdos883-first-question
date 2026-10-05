import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_132 :
    (List.ofFn coreChunks749_132).flatten =
      (coreData749.take (coreResources749 132).q).drop 307 := by
  decide +kernel

theorem coreCheck749_132 :
    ∀ c : Fin 1, (coreChunks749_132 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 132)) = true := by
  decide +kernel
#print axioms coreFlatten749_132
#print axioms coreCheck749_132
end Erdos883Verified
