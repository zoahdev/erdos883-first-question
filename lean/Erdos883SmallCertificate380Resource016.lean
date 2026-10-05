import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_16 :
    (List.ofFn coreChunks380_16).flatten =
      (coreData380.take (coreResources380 16).q).drop 89 := by
  decide +kernel

theorem coreCheck380_16 :
    ∀ c : Fin 1, (coreChunks380_16 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 16)) = true := by
  decide +kernel
#print axioms coreFlatten380_16
#print axioms coreCheck380_16
end Erdos883Verified
