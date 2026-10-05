import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_20 :
    (List.ofFn coreChunks380_20).flatten =
      (coreData380.take (coreResources380 20).q).drop 53 := by
  decide +kernel

theorem coreCheck380_20 :
    ∀ c : Fin 1, (coreChunks380_20 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 20)) = true := by
  decide +kernel
#print axioms coreFlatten380_20
#print axioms coreCheck380_20
end Erdos883Verified
