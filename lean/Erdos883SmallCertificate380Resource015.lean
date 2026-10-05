import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_15 :
    (List.ofFn coreChunks380_15).flatten =
      (coreData380.take (coreResources380 15).q).drop 88 := by
  decide +kernel

theorem coreCheck380_15 :
    ∀ c : Fin 1, (coreChunks380_15 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 15)) = true := by
  decide +kernel
#print axioms coreFlatten380_15
#print axioms coreCheck380_15
end Erdos883Verified
