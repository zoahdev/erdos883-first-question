import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_84 :
    (List.ofFn coreChunks462_84).flatten =
      (coreData462.take (coreResources462 84).q).drop 199 := by
  decide +kernel

theorem coreCheck462_84 :
    ∀ c : Fin 2, (coreChunks462_84 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 84)) = true := by
  decide +kernel
#print axioms coreFlatten462_84
#print axioms coreCheck462_84
end Erdos883Verified
