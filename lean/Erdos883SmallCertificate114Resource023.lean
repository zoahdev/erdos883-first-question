import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_23 :
    (List.ofFn coreChunks114_23).flatten =
      (coreData114.take (coreResources114 23).q).drop 37 := by
  decide +kernel

theorem coreCheck114_23 :
    ∀ c : Fin 1, (coreChunks114_23 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 23)) = true := by
  decide +kernel
#print axioms coreFlatten114_23
#print axioms coreCheck114_23
end Erdos883Verified
