import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_48 :
    (List.ofFn coreChunks462_48).flatten =
      (coreData462.take (coreResources462 48).q).drop 94 := by
  decide +kernel

theorem coreCheck462_48 :
    ∀ c : Fin 1, (coreChunks462_48 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 48)) = true := by
  decide +kernel
#print axioms coreFlatten462_48
#print axioms coreCheck462_48
end Erdos883Verified
