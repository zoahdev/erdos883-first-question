import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_57 :
    (List.ofFn coreChunks462_57).flatten =
      (coreData462.take (coreResources462 57).q).drop 107 := by
  decide +kernel

theorem coreCheck462_57 :
    ∀ c : Fin 1, (coreChunks462_57 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 57)) = true := by
  decide +kernel
#print axioms coreFlatten462_57
#print axioms coreCheck462_57
end Erdos883Verified
