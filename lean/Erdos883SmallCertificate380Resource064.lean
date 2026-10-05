import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_64 :
    (List.ofFn coreChunks380_64).flatten =
      (coreData380.take (coreResources380 64).q).drop 0 := by
  decide +kernel

theorem coreCheck380_64 :
    ∀ c : Fin 8, (coreChunks380_64 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 64)) = true := by
  decide +kernel
#print axioms coreFlatten380_64
#print axioms coreCheck380_64
end Erdos883Verified
