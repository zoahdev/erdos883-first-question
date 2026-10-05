import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_24 :
    (List.ofFn coreChunks380_24).flatten =
      (coreData380.take (coreResources380 24).q).drop 62 := by
  decide +kernel

theorem coreCheck380_24 :
    ∀ c : Fin 1, (coreChunks380_24 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 24)) = true := by
  decide +kernel
#print axioms coreFlatten380_24
#print axioms coreCheck380_24
end Erdos883Verified
