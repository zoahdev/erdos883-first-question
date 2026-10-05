import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_15 :
    (List.ofFn coreChunks114_15).flatten =
      (coreData114.take (coreResources114 15).q).drop 38 := by
  decide +kernel

theorem coreCheck114_15 :
    ∀ c : Fin 1, (coreChunks114_15 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 15)) = true := by
  decide +kernel
#print axioms coreFlatten114_15
#print axioms coreCheck114_15
end Erdos883Verified
