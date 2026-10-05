import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_3 :
    (List.ofFn coreChunks462_3).flatten =
      (coreData462.take (coreResources462 3).q).drop 56 := by
  decide +kernel

theorem coreCheck462_3 :
    ∀ c : Fin 1, (coreChunks462_3 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 3)) = true := by
  decide +kernel
#print axioms coreFlatten462_3
#print axioms coreCheck462_3
end Erdos883Verified
