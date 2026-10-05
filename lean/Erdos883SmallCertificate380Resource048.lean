import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_48 :
    (List.ofFn coreChunks380_48).flatten =
      (coreData380.take (coreResources380 48).q).drop 103 := by
  decide +kernel

theorem coreCheck380_48 :
    ∀ c : Fin 1, (coreChunks380_48 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 48)) = true := by
  decide +kernel
#print axioms coreFlatten380_48
#print axioms coreCheck380_48
end Erdos883Verified
