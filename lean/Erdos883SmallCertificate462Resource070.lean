import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_70 :
    (List.ofFn coreChunks462_70).flatten =
      (coreData462.take (coreResources462 70).q).drop 134 := by
  decide +kernel

theorem coreCheck462_70 :
    ∀ c : Fin 1, (coreChunks462_70 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 70)) = true := by
  decide +kernel
#print axioms coreFlatten462_70
#print axioms coreCheck462_70
end Erdos883Verified
