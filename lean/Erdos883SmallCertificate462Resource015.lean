import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_15 :
    (List.ofFn coreChunks462_15).flatten =
      (coreData462.take (coreResources462 15).q).drop 99 := by
  decide +kernel

theorem coreCheck462_15 :
    ∀ c : Fin 1, (coreChunks462_15 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 15)) = true := by
  decide +kernel
#print axioms coreFlatten462_15
#print axioms coreCheck462_15
end Erdos883Verified
