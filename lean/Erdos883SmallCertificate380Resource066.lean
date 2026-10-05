import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_66 :
    (List.ofFn coreChunks380_66).flatten =
      (coreData380.take (coreResources380 66).q).drop 0 := by
  decide +kernel

theorem coreCheck380_66 :
    ∀ c : Fin 7, (coreChunks380_66 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 66)) = true := by
  decide +kernel
#print axioms coreFlatten380_66
#print axioms coreCheck380_66
end Erdos883Verified
