import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_31 :
    (List.ofFn coreChunks380_31).flatten =
      (coreData380.take (coreResources380 31).q).drop 72 := by
  decide +kernel

theorem coreCheck380_31 :
    ∀ c : Fin 1, (coreChunks380_31 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 31)) = true := by
  decide +kernel
#print axioms coreFlatten380_31
#print axioms coreCheck380_31
end Erdos883Verified
