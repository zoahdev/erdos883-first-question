import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_13 :
    (List.ofFn coreChunks380_13).flatten =
      (coreData380.take (coreResources380 13).q).drop 84 := by
  decide +kernel

theorem coreCheck380_13 :
    ∀ c : Fin 1, (coreChunks380_13 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 13)) = true := by
  decide +kernel
#print axioms coreFlatten380_13
#print axioms coreCheck380_13
end Erdos883Verified
