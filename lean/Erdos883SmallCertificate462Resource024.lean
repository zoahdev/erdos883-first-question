import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_24 :
    (List.ofFn coreChunks462_24).flatten =
      (coreData462.take (coreResources462 24).q).drop 112 := by
  decide +kernel

theorem coreCheck462_24 :
    ∀ c : Fin 1, (coreChunks462_24 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 24)) = true := by
  decide +kernel
#print axioms coreFlatten462_24
#print axioms coreCheck462_24
end Erdos883Verified
