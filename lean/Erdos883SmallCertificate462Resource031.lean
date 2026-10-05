import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_31 :
    (List.ofFn coreChunks462_31).flatten =
      (coreData462.take (coreResources462 31).q).drop 71 := by
  decide +kernel

theorem coreCheck462_31 :
    ∀ c : Fin 1, (coreChunks462_31 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 31)) = true := by
  decide +kernel
#print axioms coreFlatten462_31
#print axioms coreCheck462_31
end Erdos883Verified
