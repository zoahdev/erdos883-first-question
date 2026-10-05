import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_17 :
    (List.ofFn coreChunks380_17).flatten =
      (coreData380.take (coreResources380 17).q).drop 90 := by
  decide +kernel

theorem coreCheck380_17 :
    ∀ c : Fin 1, (coreChunks380_17 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 17)) = true := by
  decide +kernel
#print axioms coreFlatten380_17
#print axioms coreCheck380_17
end Erdos883Verified
