import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_51 :
    (List.ofFn coreChunks462_51).flatten =
      (coreData462.take (coreResources462 51).q).drop 99 := by
  decide +kernel

theorem coreCheck462_51 :
    ∀ c : Fin 1, (coreChunks462_51 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 51)) = true := by
  decide +kernel
#print axioms coreFlatten462_51
#print axioms coreCheck462_51
end Erdos883Verified
