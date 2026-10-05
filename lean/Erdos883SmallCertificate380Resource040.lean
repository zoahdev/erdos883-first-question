import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_40 :
    (List.ofFn coreChunks380_40).flatten =
      (coreData380.take (coreResources380 40).q).drop 89 := by
  decide +kernel

theorem coreCheck380_40 :
    ∀ c : Fin 1, (coreChunks380_40 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 40)) = true := by
  decide +kernel
#print axioms coreFlatten380_40
#print axioms coreCheck380_40
end Erdos883Verified
