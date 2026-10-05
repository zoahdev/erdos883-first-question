import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_59 :
    (List.ofFn coreChunks380_59).flatten =
      (coreData380.take (coreResources380 59).q).drop 159 := by
  decide +kernel

theorem coreCheck380_59 :
    ∀ c : Fin 1, (coreChunks380_59 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 59)) = true := by
  decide +kernel
#print axioms coreFlatten380_59
#print axioms coreCheck380_59
end Erdos883Verified
