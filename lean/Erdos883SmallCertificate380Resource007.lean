import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_7 :
    (List.ofFn coreChunks380_7).flatten =
      (coreData380.take (coreResources380 7).q).drop 77 := by
  decide +kernel

theorem coreCheck380_7 :
    ∀ c : Fin 1, (coreChunks380_7 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 7)) = true := by
  decide +kernel
#print axioms coreFlatten380_7
#print axioms coreCheck380_7
end Erdos883Verified
