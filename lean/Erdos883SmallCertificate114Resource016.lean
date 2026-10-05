import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_16 :
    (List.ofFn coreChunks114_16).flatten =
      (coreData114.take (coreResources114 16).q).drop 42 := by
  decide +kernel

theorem coreCheck114_16 :
    ∀ c : Fin 1, (coreChunks114_16 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 16)) = true := by
  decide +kernel
#print axioms coreFlatten114_16
#print axioms coreCheck114_16
end Erdos883Verified
