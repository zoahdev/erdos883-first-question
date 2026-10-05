import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_45 :
    (List.ofFn coreChunks380_45).flatten =
      (coreData380.take (coreResources380 45).q).drop 98 := by
  decide +kernel

theorem coreCheck380_45 :
    ∀ c : Fin 1, (coreChunks380_45 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 45)) = true := by
  decide +kernel
#print axioms coreFlatten380_45
#print axioms coreCheck380_45
end Erdos883Verified
