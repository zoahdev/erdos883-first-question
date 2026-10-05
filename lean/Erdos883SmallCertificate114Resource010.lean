import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_10 :
    (List.ofFn coreChunks114_10).flatten =
      (coreData114.take (coreResources114 10).q).drop 29 := by
  decide +kernel

theorem coreCheck114_10 :
    ∀ c : Fin 1, (coreChunks114_10 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 10)) = true := by
  decide +kernel
#print axioms coreFlatten114_10
#print axioms coreCheck114_10
end Erdos883Verified
