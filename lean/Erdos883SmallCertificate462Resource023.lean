import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_23 :
    (List.ofFn coreChunks462_23).flatten =
      (coreData462.take (coreResources462 23).q).drop 111 := by
  decide +kernel

theorem coreCheck462_23 :
    ∀ c : Fin 1, (coreChunks462_23 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 23)) = true := by
  decide +kernel
#print axioms coreFlatten462_23
#print axioms coreCheck462_23
end Erdos883Verified
