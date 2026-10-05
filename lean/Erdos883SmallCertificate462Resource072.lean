import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_72 :
    (List.ofFn coreChunks462_72).flatten =
      (coreData462.take (coreResources462 72).q).drop 139 := by
  decide +kernel

theorem coreCheck462_72 :
    ∀ c : Fin 1, (coreChunks462_72 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 72)) = true := by
  decide +kernel
#print axioms coreFlatten462_72
#print axioms coreCheck462_72
end Erdos883Verified
