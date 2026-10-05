import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_56 :
    (List.ofFn coreChunks380_56).flatten =
      (coreData380.take (coreResources380 56).q).drop 132 := by
  decide +kernel

theorem coreCheck380_56 :
    ∀ c : Fin 1, (coreChunks380_56 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 56)) = true := by
  decide +kernel
#print axioms coreFlatten380_56
#print axioms coreCheck380_56
end Erdos883Verified
