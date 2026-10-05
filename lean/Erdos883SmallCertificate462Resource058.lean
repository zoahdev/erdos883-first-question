import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_58 :
    (List.ofFn coreChunks462_58).flatten =
      (coreData462.take (coreResources462 58).q).drop 108 := by
  decide +kernel

theorem coreCheck462_58 :
    ∀ c : Fin 1, (coreChunks462_58 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 58)) = true := by
  decide +kernel
#print axioms coreFlatten462_58
#print axioms coreCheck462_58
end Erdos883Verified
