import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_32 :
    (List.ofFn coreChunks462_32).flatten =
      (coreData462.take (coreResources462 32).q).drop 72 := by
  decide +kernel

theorem coreCheck462_32 :
    ∀ c : Fin 1, (coreChunks462_32 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 32)) = true := by
  decide +kernel
#print axioms coreFlatten462_32
#print axioms coreCheck462_32
end Erdos883Verified
