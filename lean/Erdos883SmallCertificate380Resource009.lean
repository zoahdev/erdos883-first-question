import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_9 :
    (List.ofFn coreChunks380_9).flatten =
      (coreData380.take (coreResources380 9).q).drop 79 := by
  decide +kernel

theorem coreCheck380_9 :
    ∀ c : Fin 1, (coreChunks380_9 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 9)) = true := by
  decide +kernel
#print axioms coreFlatten380_9
#print axioms coreCheck380_9
end Erdos883Verified
