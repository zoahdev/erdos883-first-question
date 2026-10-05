import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_1 :
    (List.ofFn coreChunks380_1).flatten =
      (coreData380.take (coreResources380 1).q).drop 36 := by
  decide +kernel

theorem coreCheck380_1 :
    ∀ c : Fin 1, (coreChunks380_1 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 1)) = true := by
  decide +kernel
#print axioms coreFlatten380_1
#print axioms coreCheck380_1
end Erdos883Verified
