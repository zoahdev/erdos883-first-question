import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_54 :
    (List.ofFn coreChunks380_54).flatten =
      (coreData380.take (coreResources380 54).q).drop 120 := by
  decide +kernel

theorem coreCheck380_54 :
    ∀ c : Fin 1, (coreChunks380_54 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 54)) = true := by
  decide +kernel
#print axioms coreFlatten380_54
#print axioms coreCheck380_54
end Erdos883Verified
