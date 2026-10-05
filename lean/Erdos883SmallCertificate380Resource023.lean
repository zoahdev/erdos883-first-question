import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_23 :
    (List.ofFn coreChunks380_23).flatten =
      (coreData380.take (coreResources380 23).q).drop 61 := by
  decide +kernel

theorem coreCheck380_23 :
    ∀ c : Fin 1, (coreChunks380_23 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 23)) = true := by
  decide +kernel
#print axioms coreFlatten380_23
#print axioms coreCheck380_23
end Erdos883Verified
