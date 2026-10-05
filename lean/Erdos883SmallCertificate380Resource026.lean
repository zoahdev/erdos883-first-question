import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_26 :
    (List.ofFn coreChunks380_26).flatten =
      (coreData380.take (coreResources380 26).q).drop 65 := by
  decide +kernel

theorem coreCheck380_26 :
    ∀ c : Fin 1, (coreChunks380_26 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 26)) = true := by
  decide +kernel
#print axioms coreFlatten380_26
#print axioms coreCheck380_26
end Erdos883Verified
