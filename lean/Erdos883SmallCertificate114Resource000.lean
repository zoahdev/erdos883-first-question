import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_0 :
    (List.ofFn coreChunks114_0).flatten =
      (coreData114.take (coreResources114 0).q).drop 0 := by
  decide +kernel

theorem coreCheck114_0 :
    ∀ c : Fin 1, (coreChunks114_0 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 0)) = true := by
  decide +kernel
#print axioms coreFlatten114_0
#print axioms coreCheck114_0
end Erdos883Verified
