import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_53 :
    (List.ofFn coreChunks462_53).flatten =
      (coreData462.take (coreResources462 53).q).drop 101 := by
  decide +kernel

theorem coreCheck462_53 :
    ∀ c : Fin 1, (coreChunks462_53 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 53)) = true := by
  decide +kernel
#print axioms coreFlatten462_53
#print axioms coreCheck462_53
end Erdos883Verified
