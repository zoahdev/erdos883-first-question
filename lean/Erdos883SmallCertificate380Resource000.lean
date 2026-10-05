import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_0 :
    (List.ofFn coreChunks380_0).flatten =
      (coreData380.take (coreResources380 0).q).drop 0 := by
  decide +kernel

theorem coreCheck380_0 :
    ∀ c : Fin 3, (coreChunks380_0 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 0)) = true := by
  decide +kernel
#print axioms coreFlatten380_0
#print axioms coreCheck380_0
end Erdos883Verified
