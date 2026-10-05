import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_4 :
    (List.ofFn coreChunks380_4).flatten =
      (coreData380.take (coreResources380 4).q).drop 47 := by
  decide +kernel

theorem coreCheck380_4 :
    ∀ c : Fin 1, (coreChunks380_4 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 4)) = true := by
  decide +kernel
#print axioms coreFlatten380_4
#print axioms coreCheck380_4
end Erdos883Verified
