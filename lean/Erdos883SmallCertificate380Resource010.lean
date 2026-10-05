import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_10 :
    (List.ofFn coreChunks380_10).flatten =
      (coreData380.take (coreResources380 10).q).drop 81 := by
  decide +kernel

theorem coreCheck380_10 :
    ∀ c : Fin 1, (coreChunks380_10 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 10)) = true := by
  decide +kernel
#print axioms coreFlatten380_10
#print axioms coreCheck380_10
end Erdos883Verified
