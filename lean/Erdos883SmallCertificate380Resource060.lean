import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_60 :
    (List.ofFn coreChunks380_60).flatten =
      (coreData380.take (coreResources380 60).q).drop 163 := by
  decide +kernel

theorem coreCheck380_60 :
    ∀ c : Fin 1, (coreChunks380_60 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 60)) = true := by
  decide +kernel
#print axioms coreFlatten380_60
#print axioms coreCheck380_60
end Erdos883Verified
