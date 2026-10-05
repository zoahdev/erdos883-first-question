import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_35 :
    (List.ofFn coreChunks380_35).flatten =
      (coreData380.take (coreResources380 35).q).drop 78 := by
  decide +kernel

theorem coreCheck380_35 :
    ∀ c : Fin 1, (coreChunks380_35 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 35)) = true := by
  decide +kernel
#print axioms coreFlatten380_35
#print axioms coreCheck380_35
end Erdos883Verified
