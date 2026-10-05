import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_17 :
    (List.ofFn coreChunks462_17).flatten =
      (coreData462.take (coreResources462 17).q).drop 101 := by
  decide +kernel

theorem coreCheck462_17 :
    ∀ c : Fin 1, (coreChunks462_17 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 17)) = true := by
  decide +kernel
#print axioms coreFlatten462_17
#print axioms coreCheck462_17
end Erdos883Verified
