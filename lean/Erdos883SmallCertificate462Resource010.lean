import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_10 :
    (List.ofFn coreChunks462_10).flatten =
      (coreData462.take (coreResources462 10).q).drop 93 := by
  decide +kernel

theorem coreCheck462_10 :
    ∀ c : Fin 1, (coreChunks462_10 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 10)) = true := by
  decide +kernel
#print axioms coreFlatten462_10
#print axioms coreCheck462_10
end Erdos883Verified
