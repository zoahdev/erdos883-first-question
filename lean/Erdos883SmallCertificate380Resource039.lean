import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_39 :
    (List.ofFn coreChunks380_39).flatten =
      (coreData380.take (coreResources380 39).q).drop 84 := by
  decide +kernel

theorem coreCheck380_39 :
    ∀ c : Fin 1, (coreChunks380_39 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 39)) = true := by
  decide +kernel
#print axioms coreFlatten380_39
#print axioms coreCheck380_39
end Erdos883Verified
