import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_14 :
    (List.ofFn coreChunks380_14).flatten =
      (coreData380.take (coreResources380 14).q).drop 85 := by
  decide +kernel

theorem coreCheck380_14 :
    ∀ c : Fin 1, (coreChunks380_14 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 14)) = true := by
  decide +kernel
#print axioms coreFlatten380_14
#print axioms coreCheck380_14
end Erdos883Verified
