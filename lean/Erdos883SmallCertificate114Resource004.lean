import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_4 :
    (List.ofFn coreChunks114_4).flatten =
      (coreData114.take (coreResources114 4).q).drop 22 := by
  decide +kernel

theorem coreCheck114_4 :
    ∀ c : Fin 1, (coreChunks114_4 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 4)) = true := by
  decide +kernel
#print axioms coreFlatten114_4
#print axioms coreCheck114_4
end Erdos883Verified
