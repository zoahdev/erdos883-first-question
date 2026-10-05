import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_1 :
    (List.ofFn coreChunks114_1).flatten =
      (coreData114.take (coreResources114 1).q).drop 0 := by
  decide +kernel

theorem coreCheck114_1 :
    ∀ c : Fin 1, (coreChunks114_1 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 1)) = true := by
  decide +kernel
#print axioms coreFlatten114_1
#print axioms coreCheck114_1
end Erdos883Verified
