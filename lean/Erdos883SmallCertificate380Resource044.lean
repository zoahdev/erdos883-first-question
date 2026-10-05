import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten380_44 :
    (List.ofFn coreChunks380_44).flatten =
      (coreData380.take (coreResources380 44).q).drop 97 := by
  decide +kernel

theorem coreCheck380_44 :
    ∀ c : Fin 1, (coreChunks380_44 c).all
      (coreResourceRowCheck 346 coreData380 (coreResources380 44)) = true := by
  decide +kernel
#print axioms coreFlatten380_44
#print axioms coreCheck380_44
end Erdos883Verified
