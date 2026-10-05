import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_28 :
    (List.ofFn coreChunks380_28).flatten =
      (coreData380.take (coreResources380 28).q).drop 67 := by
  decide +kernel

theorem coreCheck380_28 :
    ∀ c : Fin 1, (coreChunks380_28 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 28)) = true := by
  decide +kernel
#print axioms coreFlatten380_28
#print axioms coreCheck380_28
end Erdos883Verified
