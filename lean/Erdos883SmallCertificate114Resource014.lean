import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_14 :
    (List.ofFn coreChunks114_14).flatten =
      (coreData114.take (coreResources114 14).q).drop 35 := by
  decide +kernel

theorem coreCheck114_14 :
    ∀ c : Fin 1, (coreChunks114_14 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 14)) = true := by
  decide +kernel
#print axioms coreFlatten114_14
#print axioms coreCheck114_14
end Erdos883Verified
