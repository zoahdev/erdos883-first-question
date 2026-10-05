import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_19 :
    (List.ofFn coreChunks380_19).flatten =
      (coreData380.take (coreResources380 19).q).drop 0 := by
  decide +kernel

theorem coreCheck380_19 :
    ∀ c : Fin 4, (coreChunks380_19 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 19)) = true := by
  decide +kernel
#print axioms coreFlatten380_19
#print axioms coreCheck380_19
end Erdos883Verified
