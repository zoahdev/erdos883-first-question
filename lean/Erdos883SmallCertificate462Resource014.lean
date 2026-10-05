import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_14 :
    (List.ofFn coreChunks462_14).flatten =
      (coreData462.take (coreResources462 14).q).drop 98 := by
  decide +kernel

theorem coreCheck462_14 :
    ∀ c : Fin 1, (coreChunks462_14 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 14)) = true := by
  decide +kernel
#print axioms coreFlatten462_14
#print axioms coreCheck462_14
end Erdos883Verified
