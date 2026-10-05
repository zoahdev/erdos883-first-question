import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_36 :
    (List.ofFn coreChunks380_36).flatten =
      (coreData380.take (coreResources380 36).q).drop 81 := by
  decide +kernel

theorem coreCheck380_36 :
    ∀ c : Fin 1, (coreChunks380_36 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 36)) = true := by
  decide +kernel
#print axioms coreFlatten380_36
#print axioms coreCheck380_36
end Erdos883Verified
