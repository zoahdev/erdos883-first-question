import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_11 :
    (List.ofFn coreChunks380_11).flatten =
      (coreData380.take (coreResources380 11).q).drop 82 := by
  decide +kernel

theorem coreCheck380_11 :
    ∀ c : Fin 1, (coreChunks380_11 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 11)) = true := by
  decide +kernel
#print axioms coreFlatten380_11
#print axioms coreCheck380_11
end Erdos883Verified
