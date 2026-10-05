import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_43 :
    (List.ofFn coreChunks380_43).flatten =
      (coreData380.take (coreResources380 43).q).drop 95 := by
  decide +kernel

theorem coreCheck380_43 :
    ∀ c : Fin 1, (coreChunks380_43 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 43)) = true := by
  decide +kernel
#print axioms coreFlatten380_43
#print axioms coreCheck380_43
end Erdos883Verified
