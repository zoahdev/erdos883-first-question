import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_63 :
    (List.ofFn coreChunks380_63).flatten =
      (coreData380.take (coreResources380 63).q).drop 0 := by
  decide +kernel

theorem coreCheck380_63 :
    ∀ c : Fin 10, (coreChunks380_63 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 63)) = true := by
  decide +kernel
#print axioms coreFlatten380_63
#print axioms coreCheck380_63
end Erdos883Verified
