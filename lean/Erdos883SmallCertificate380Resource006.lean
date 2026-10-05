import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_6 :
    (List.ofFn coreChunks380_6).flatten =
      (coreData380.take (coreResources380 6).q).drop 75 := by
  decide +kernel

theorem coreCheck380_6 :
    ∀ c : Fin 1, (coreChunks380_6 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 6)) = true := by
  decide +kernel
#print axioms coreFlatten380_6
#print axioms coreCheck380_6
end Erdos883Verified
