import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_62 :
    (List.ofFn coreChunks380_62).flatten =
      (coreData380.take (coreResources380 62).q).drop 181 := by
  decide +kernel

theorem coreCheck380_62 :
    ∀ c : Fin 1, (coreChunks380_62 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 62)) = true := by
  decide +kernel
#print axioms coreFlatten380_62
#print axioms coreCheck380_62
end Erdos883Verified
