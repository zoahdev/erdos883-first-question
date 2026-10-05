import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_9 :
    (List.ofFn coreChunks114_9).flatten =
      (coreData114.take (coreResources114 9).q).drop 27 := by
  decide +kernel

theorem coreCheck114_9 :
    ∀ c : Fin 1, (coreChunks114_9 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 9)) = true := by
  decide +kernel
#print axioms coreFlatten114_9
#print axioms coreCheck114_9
end Erdos883Verified
