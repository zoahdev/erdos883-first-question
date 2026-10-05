import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_32 :
    (List.ofFn coreChunks380_32).flatten =
      (coreData380.take (coreResources380 32).q).drop 74 := by
  decide +kernel

theorem coreCheck380_32 :
    ∀ c : Fin 1, (coreChunks380_32 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 32)) = true := by
  decide +kernel
#print axioms coreFlatten380_32
#print axioms coreCheck380_32
end Erdos883Verified
