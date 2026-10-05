import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_42 :
    (List.ofFn coreChunks462_42).flatten =
      (coreData462.take (coreResources462 42).q).drop 86 := by
  decide +kernel

theorem coreCheck462_42 :
    ∀ c : Fin 1, (coreChunks462_42 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 42)) = true := by
  decide +kernel
#print axioms coreFlatten462_42
#print axioms coreCheck462_42
end Erdos883Verified
