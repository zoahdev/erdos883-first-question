import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_61 :
    (List.ofFn coreChunks380_61).flatten =
      (coreData380.take (coreResources380 61).q).drop 174 := by
  decide +kernel

theorem coreCheck380_61 :
    ∀ c : Fin 1, (coreChunks380_61 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 61)) = true := by
  decide +kernel
#print axioms coreFlatten380_61
#print axioms coreCheck380_61
end Erdos883Verified
