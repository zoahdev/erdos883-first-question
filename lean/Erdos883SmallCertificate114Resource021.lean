import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_21 :
    (List.ofFn coreChunks114_21).flatten =
      (coreData114.take (coreResources114 21).q).drop 35 := by
  decide +kernel

theorem coreCheck114_21 :
    ∀ c : Fin 1, (coreChunks114_21 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 21)) = true := by
  decide +kernel
#print axioms coreFlatten114_21
#print axioms coreCheck114_21
end Erdos883Verified
