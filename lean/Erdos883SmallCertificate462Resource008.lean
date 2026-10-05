import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_8 :
    (List.ofFn coreChunks462_8).flatten =
      (coreData462.take (coreResources462 8).q).drop 91 := by
  decide +kernel

theorem coreCheck462_8 :
    ∀ c : Fin 1, (coreChunks462_8 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 8)) = true := by
  decide +kernel
#print axioms coreFlatten462_8
#print axioms coreCheck462_8
end Erdos883Verified
