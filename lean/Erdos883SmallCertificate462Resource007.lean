import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_7 :
    (List.ofFn coreChunks462_7).flatten =
      (coreData462.take (coreResources462 7).q).drop 90 := by
  decide +kernel

theorem coreCheck462_7 :
    ∀ c : Fin 1, (coreChunks462_7 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 7)) = true := by
  decide +kernel
#print axioms coreFlatten462_7
#print axioms coreCheck462_7
end Erdos883Verified
