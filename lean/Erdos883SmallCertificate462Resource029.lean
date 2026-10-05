import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_29 :
    (List.ofFn coreChunks462_29).flatten =
      (coreData462.take (coreResources462 29).q).drop 63 := by
  decide +kernel

theorem coreCheck462_29 :
    ∀ c : Fin 1, (coreChunks462_29 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 29)) = true := by
  decide +kernel
#print axioms coreFlatten462_29
#print axioms coreCheck462_29
end Erdos883Verified
