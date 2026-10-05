import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_51 :
    (List.ofFn coreChunks380_51).flatten =
      (coreData380.take (coreResources380 51).q).drop 111 := by
  decide +kernel

theorem coreCheck380_51 :
    ∀ c : Fin 1, (coreChunks380_51 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 51)) = true := by
  decide +kernel
#print axioms coreFlatten380_51
#print axioms coreCheck380_51
end Erdos883Verified
