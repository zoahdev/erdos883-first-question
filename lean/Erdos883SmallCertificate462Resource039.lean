import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_39 :
    (List.ofFn coreChunks462_39).flatten =
      (coreData462.take (coreResources462 39).q).drop 81 := by
  decide +kernel

theorem coreCheck462_39 :
    ∀ c : Fin 1, (coreChunks462_39 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 39)) = true := by
  decide +kernel
#print axioms coreFlatten462_39
#print axioms coreCheck462_39
end Erdos883Verified
