import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_47 :
    (List.ofFn coreChunks380_47).flatten =
      (coreData380.take (coreResources380 47).q).drop 100 := by
  decide +kernel

theorem coreCheck380_47 :
    ∀ c : Fin 1, (coreChunks380_47 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 47)) = true := by
  decide +kernel
#print axioms coreFlatten380_47
#print axioms coreCheck380_47
end Erdos883Verified
