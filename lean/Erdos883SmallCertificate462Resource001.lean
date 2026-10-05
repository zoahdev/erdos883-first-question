import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_1 :
    (List.ofFn coreChunks462_1).flatten =
      (coreData462.take (coreResources462 1).q).drop 44 := by
  decide +kernel

theorem coreCheck462_1 :
    ∀ c : Fin 1, (coreChunks462_1 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 1)) = true := by
  decide +kernel
#print axioms coreFlatten462_1
#print axioms coreCheck462_1
end Erdos883Verified
