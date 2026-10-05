import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_79 :
    (List.ofFn coreChunks462_79).flatten =
      (coreData462.take (coreResources462 79).q).drop 178 := by
  decide +kernel

theorem coreCheck462_79 :
    ∀ c : Fin 1, (coreChunks462_79 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 79)) = true := by
  decide +kernel
#print axioms coreFlatten462_79
#print axioms coreCheck462_79
end Erdos883Verified
