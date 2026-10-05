import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_25 :
    (List.ofFn coreChunks380_25).flatten =
      (coreData380.take (coreResources380 25).q).drop 63 := by
  decide +kernel

theorem coreCheck380_25 :
    ∀ c : Fin 1, (coreChunks380_25 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 25)) = true := by
  decide +kernel
#print axioms coreFlatten380_25
#print axioms coreCheck380_25
end Erdos883Verified
