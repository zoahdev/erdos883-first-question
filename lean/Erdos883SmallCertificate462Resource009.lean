import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_9 :
    (List.ofFn coreChunks462_9).flatten =
      (coreData462.take (coreResources462 9).q).drop 92 := by
  decide +kernel

theorem coreCheck462_9 :
    ∀ c : Fin 1, (coreChunks462_9 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 9)) = true := by
  decide +kernel
#print axioms coreFlatten462_9
#print axioms coreCheck462_9
end Erdos883Verified
