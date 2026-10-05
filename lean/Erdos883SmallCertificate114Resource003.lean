import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_3 :
    (List.ofFn coreChunks114_3).flatten =
      (coreData114.take (coreResources114 3).q).drop 17 := by
  decide +kernel

theorem coreCheck114_3 :
    ∀ c : Fin 1, (coreChunks114_3 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 3)) = true := by
  decide +kernel
#print axioms coreFlatten114_3
#print axioms coreCheck114_3
end Erdos883Verified
