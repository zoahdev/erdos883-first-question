import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_64 :
    (List.ofFn coreChunks462_64).flatten =
      (coreData462.take (coreResources462 64).q).drop 119 := by
  decide +kernel

theorem coreCheck462_64 :
    ∀ c : Fin 1, (coreChunks462_64 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 64)) = true := by
  decide +kernel
#print axioms coreFlatten462_64
#print axioms coreCheck462_64
end Erdos883Verified
