import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_53 :
    (List.ofFn coreChunks380_53).flatten =
      (coreData380.take (coreResources380 53).q).drop 118 := by
  decide +kernel

theorem coreCheck380_53 :
    ∀ c : Fin 1, (coreChunks380_53 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 53)) = true := by
  decide +kernel
#print axioms coreFlatten380_53
#print axioms coreCheck380_53
end Erdos883Verified
