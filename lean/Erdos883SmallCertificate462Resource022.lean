import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_22 :
    (List.ofFn coreChunks462_22).flatten =
      (coreData462.take (coreResources462 22).q).drop 108 := by
  decide +kernel

theorem coreCheck462_22 :
    ∀ c : Fin 1, (coreChunks462_22 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 22)) = true := by
  decide +kernel
#print axioms coreFlatten462_22
#print axioms coreCheck462_22
end Erdos883Verified
