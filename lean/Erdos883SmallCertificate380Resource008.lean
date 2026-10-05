import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_8 :
    (List.ofFn coreChunks380_8).flatten =
      (coreData380.take (coreResources380 8).q).drop 78 := by
  decide +kernel

theorem coreCheck380_8 :
    ∀ c : Fin 1, (coreChunks380_8 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 8)) = true := by
  decide +kernel
#print axioms coreFlatten380_8
#print axioms coreCheck380_8
end Erdos883Verified
