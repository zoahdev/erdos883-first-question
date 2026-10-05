import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_22 :
    (List.ofFn coreChunks380_22).flatten =
      (coreData380.take (coreResources380 22).q).drop 60 := by
  decide +kernel

theorem coreCheck380_22 :
    ∀ c : Fin 1, (coreChunks380_22 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 22)) = true := by
  decide +kernel
#print axioms coreFlatten380_22
#print axioms coreCheck380_22
end Erdos883Verified
