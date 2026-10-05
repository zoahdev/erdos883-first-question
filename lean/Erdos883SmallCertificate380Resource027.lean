import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_27 :
    (List.ofFn coreChunks380_27).flatten =
      (coreData380.take (coreResources380 27).q).drop 66 := by
  decide +kernel

theorem coreCheck380_27 :
    ∀ c : Fin 1, (coreChunks380_27 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 27)) = true := by
  decide +kernel
#print axioms coreFlatten380_27
#print axioms coreCheck380_27
end Erdos883Verified
