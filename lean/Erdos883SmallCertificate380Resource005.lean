import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_5 :
    (List.ofFn coreChunks380_5).flatten =
      (coreData380.take (coreResources380 5).q).drop 50 := by
  decide +kernel

theorem coreCheck380_5 :
    ∀ c : Fin 2, (coreChunks380_5 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 5)) = true := by
  decide +kernel
#print axioms coreFlatten380_5
#print axioms coreCheck380_5
end Erdos883Verified
