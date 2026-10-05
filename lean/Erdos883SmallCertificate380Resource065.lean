import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_65 :
    (List.ofFn coreChunks380_65).flatten =
      (coreData380.take (coreResources380 65).q).drop 0 := by
  decide +kernel

theorem coreCheck380_65 :
    ∀ c : Fin 7, (coreChunks380_65 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 65)) = true := by
  decide +kernel
#print axioms coreFlatten380_65
#print axioms coreCheck380_65
end Erdos883Verified
