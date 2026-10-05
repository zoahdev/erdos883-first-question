import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_17 :
    (List.ofFn coreChunks114_17).flatten =
      (coreData114.take (coreResources114 17).q).drop 45 := by
  decide +kernel

theorem coreCheck114_17 :
    ∀ c : Fin 1, (coreChunks114_17 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 17)) = true := by
  decide +kernel
#print axioms coreFlatten114_17
#print axioms coreCheck114_17
end Erdos883Verified
