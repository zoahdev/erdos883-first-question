import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_38 :
    (List.ofFn coreChunks380_38).flatten =
      (coreData380.take (coreResources380 38).q).drop 83 := by
  decide +kernel

theorem coreCheck380_38 :
    ∀ c : Fin 1, (coreChunks380_38 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 38)) = true := by
  decide +kernel
#print axioms coreFlatten380_38
#print axioms coreCheck380_38
end Erdos883Verified
