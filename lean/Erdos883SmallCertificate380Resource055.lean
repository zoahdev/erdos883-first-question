import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_55 :
    (List.ofFn coreChunks380_55).flatten =
      (coreData380.take (coreResources380 55).q).drop 127 := by
  decide +kernel

theorem coreCheck380_55 :
    ∀ c : Fin 1, (coreChunks380_55 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 55)) = true := by
  decide +kernel
#print axioms coreFlatten380_55
#print axioms coreCheck380_55
end Erdos883Verified
