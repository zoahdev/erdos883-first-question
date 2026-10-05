import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_57 :
    (List.ofFn coreChunks380_57).flatten =
      (coreData380.take (coreResources380 57).q).drop 139 := by
  decide +kernel

theorem coreCheck380_57 :
    ∀ c : Fin 1, (coreChunks380_57 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 57)) = true := by
  decide +kernel
#print axioms coreFlatten380_57
#print axioms coreCheck380_57
end Erdos883Verified
