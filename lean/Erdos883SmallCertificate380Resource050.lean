import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_50 :
    (List.ofFn coreChunks380_50).flatten =
      (coreData380.take (coreResources380 50).q).drop 109 := by
  decide +kernel

theorem coreCheck380_50 :
    ∀ c : Fin 1, (coreChunks380_50 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 50)) = true := by
  decide +kernel
#print axioms coreFlatten380_50
#print axioms coreCheck380_50
end Erdos883Verified
