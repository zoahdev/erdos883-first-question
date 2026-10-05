import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_5 :
    (List.ofFn coreChunks114_5).flatten =
      (coreData114.take (coreResources114 5).q).drop 23 := by
  decide +kernel

theorem coreCheck114_5 :
    ∀ c : Fin 1, (coreChunks114_5 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 5)) = true := by
  decide +kernel
#print axioms coreFlatten114_5
#print axioms coreCheck114_5
end Erdos883Verified
