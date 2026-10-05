import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_58 :
    (List.ofFn coreChunks380_58).flatten =
      (coreData380.take (coreResources380 58).q).drop 148 := by
  decide +kernel

theorem coreCheck380_58 :
    ∀ c : Fin 1, (coreChunks380_58 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 58)) = true := by
  decide +kernel
#print axioms coreFlatten380_58
#print axioms coreCheck380_58
end Erdos883Verified
