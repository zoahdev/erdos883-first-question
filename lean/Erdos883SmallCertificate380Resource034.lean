import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_34 :
    (List.ofFn coreChunks380_34).flatten =
      (coreData380.take (coreResources380 34).q).drop 77 := by
  decide +kernel

theorem coreCheck380_34 :
    ∀ c : Fin 1, (coreChunks380_34 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 34)) = true := by
  decide +kernel
#print axioms coreFlatten380_34
#print axioms coreCheck380_34
end Erdos883Verified
