import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_22 :
    (List.ofFn coreChunks114_22).flatten =
      (coreData114.take (coreResources114 22).q).drop 36 := by
  decide +kernel

theorem coreCheck114_22 :
    ∀ c : Fin 1, (coreChunks114_22 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 22)) = true := by
  decide +kernel
#print axioms coreFlatten114_22
#print axioms coreCheck114_22
end Erdos883Verified
