import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_30 :
    (List.ofFn coreChunks380_30).flatten =
      (coreData380.take (coreResources380 30).q).drop 70 := by
  decide +kernel

theorem coreCheck380_30 :
    ∀ c : Fin 1, (coreChunks380_30 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 30)) = true := by
  decide +kernel
#print axioms coreFlatten380_30
#print axioms coreCheck380_30
end Erdos883Verified
