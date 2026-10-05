import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_59 :
    (List.ofFn coreChunks462_59).flatten =
      (coreData462.take (coreResources462 59).q).drop 111 := by
  decide +kernel

theorem coreCheck462_59 :
    ∀ c : Fin 1, (coreChunks462_59 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 59)) = true := by
  decide +kernel
#print axioms coreFlatten462_59
#print axioms coreCheck462_59
end Erdos883Verified
