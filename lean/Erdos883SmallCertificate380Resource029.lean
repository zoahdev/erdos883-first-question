import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_29 :
    (List.ofFn coreChunks380_29).flatten =
      (coreData380.take (coreResources380 29).q).drop 68 := by
  decide +kernel

theorem coreCheck380_29 :
    ∀ c : Fin 1, (coreChunks380_29 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 29)) = true := by
  decide +kernel
#print axioms coreFlatten380_29
#print axioms coreCheck380_29
end Erdos883Verified
