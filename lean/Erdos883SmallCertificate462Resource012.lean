import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_12 :
    (List.ofFn coreChunks462_12).flatten =
      (coreData462.take (coreResources462 12).q).drop 95 := by
  decide +kernel

theorem coreCheck462_12 :
    ∀ c : Fin 1, (coreChunks462_12 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 12)) = true := by
  decide +kernel
#print axioms coreFlatten462_12
#print axioms coreCheck462_12
end Erdos883Verified
