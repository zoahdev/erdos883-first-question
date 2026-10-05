import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_16 :
    (List.ofFn coreChunks462_16).flatten =
      (coreData462.take (coreResources462 16).q).drop 100 := by
  decide +kernel

theorem coreCheck462_16 :
    ∀ c : Fin 1, (coreChunks462_16 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 16)) = true := by
  decide +kernel
#print axioms coreFlatten462_16
#print axioms coreCheck462_16
end Erdos883Verified
