import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_21 :
    (List.ofFn coreChunks380_21).flatten =
      (coreData380.take (coreResources380 21).q).drop 54 := by
  decide +kernel

theorem coreCheck380_21 :
    ∀ c : Fin 1, (coreChunks380_21 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 21)) = true := by
  decide +kernel
#print axioms coreFlatten380_21
#print axioms coreCheck380_21
end Erdos883Verified
