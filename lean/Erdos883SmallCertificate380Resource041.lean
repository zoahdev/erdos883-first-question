import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_41 :
    (List.ofFn coreChunks380_41).flatten =
      (coreData380.take (coreResources380 41).q).drop 90 := by
  decide +kernel

theorem coreCheck380_41 :
    ∀ c : Fin 1, (coreChunks380_41 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 41)) = true := by
  decide +kernel
#print axioms coreFlatten380_41
#print axioms coreCheck380_41
end Erdos883Verified
