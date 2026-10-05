import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_12 :
    (List.ofFn coreChunks380_12).flatten =
      (coreData380.take (coreResources380 12).q).drop 83 := by
  decide +kernel

theorem coreCheck380_12 :
    ∀ c : Fin 1, (coreChunks380_12 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 12)) = true := by
  decide +kernel
#print axioms coreFlatten380_12
#print axioms coreCheck380_12
end Erdos883Verified
