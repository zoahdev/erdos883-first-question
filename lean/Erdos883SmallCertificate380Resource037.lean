import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_37 :
    (List.ofFn coreChunks380_37).flatten =
      (coreData380.take (coreResources380 37).q).drop 82 := by
  decide +kernel

theorem coreCheck380_37 :
    ∀ c : Fin 1, (coreChunks380_37 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 37)) = true := by
  decide +kernel
#print axioms coreFlatten380_37
#print axioms coreCheck380_37
end Erdos883Verified
