import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_46 :
    (List.ofFn coreChunks380_46).flatten =
      (coreData380.take (coreResources380 46).q).drop 99 := by
  decide +kernel

theorem coreCheck380_46 :
    ∀ c : Fin 1, (coreChunks380_46 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 46)) = true := by
  decide +kernel
#print axioms coreFlatten380_46
#print axioms coreCheck380_46
end Erdos883Verified
