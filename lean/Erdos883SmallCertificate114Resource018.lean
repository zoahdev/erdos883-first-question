import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_18 :
    (List.ofFn coreChunks114_18).flatten =
      (coreData114.take (coreResources114 18).q).drop 48 := by
  decide +kernel

theorem coreCheck114_18 :
    ∀ c : Fin 1, (coreChunks114_18 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 18)) = true := by
  decide +kernel
#print axioms coreFlatten114_18
#print axioms coreCheck114_18
end Erdos883Verified
