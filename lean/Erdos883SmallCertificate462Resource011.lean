import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_11 :
    (List.ofFn coreChunks462_11).flatten =
      (coreData462.take (coreResources462 11).q).drop 94 := by
  decide +kernel

theorem coreCheck462_11 :
    ∀ c : Fin 1, (coreChunks462_11 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 11)) = true := by
  decide +kernel
#print axioms coreFlatten462_11
#print axioms coreCheck462_11
end Erdos883Verified
