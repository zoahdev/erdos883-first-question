import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_18 :
    (List.ofFn coreChunks380_18).flatten =
      (coreData380.take (coreResources380 18).q).drop 92 := by
  decide +kernel

theorem coreCheck380_18 :
    ∀ c : Fin 1, (coreChunks380_18 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 18)) = true := by
  decide +kernel
#print axioms coreFlatten380_18
#print axioms coreCheck380_18
end Erdos883Verified
