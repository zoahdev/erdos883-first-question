import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_41 :
    (List.ofFn coreChunks462_41).flatten =
      (coreData462.take (coreResources462 41).q).drop 84 := by
  decide +kernel

theorem coreCheck462_41 :
    ∀ c : Fin 1, (coreChunks462_41 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 41)) = true := by
  decide +kernel
#print axioms coreFlatten462_41
#print axioms coreCheck462_41
end Erdos883Verified
