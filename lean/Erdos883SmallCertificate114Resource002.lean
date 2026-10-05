import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_2 :
    (List.ofFn coreChunks114_2).flatten =
      (coreData114.take (coreResources114 2).q).drop 16 := by
  decide +kernel

theorem coreCheck114_2 :
    ∀ c : Fin 1, (coreChunks114_2 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 2)) = true := by
  decide +kernel
#print axioms coreFlatten114_2
#print axioms coreCheck114_2
end Erdos883Verified
