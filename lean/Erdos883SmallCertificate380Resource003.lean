import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_3 :
    (List.ofFn coreChunks380_3).flatten =
      (coreData380.take (coreResources380 3).q).drop 46 := by
  decide +kernel

theorem coreCheck380_3 :
    ∀ c : Fin 1, (coreChunks380_3 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 3)) = true := by
  decide +kernel
#print axioms coreFlatten380_3
#print axioms coreCheck380_3
end Erdos883Verified
