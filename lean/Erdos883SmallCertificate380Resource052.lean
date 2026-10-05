import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_52 :
    (List.ofFn coreChunks380_52).flatten =
      (coreData380.take (coreResources380 52).q).drop 117 := by
  decide +kernel

theorem coreCheck380_52 :
    ∀ c : Fin 1, (coreChunks380_52 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 52)) = true := by
  decide +kernel
#print axioms coreFlatten380_52
#print axioms coreCheck380_52
end Erdos883Verified
