import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_18 :
    (List.ofFn coreChunks462_18).flatten =
      (coreData462.take (coreResources462 18).q).drop 102 := by
  decide +kernel

theorem coreCheck462_18 :
    ∀ c : Fin 1, (coreChunks462_18 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 18)) = true := by
  decide +kernel
#print axioms coreFlatten462_18
#print axioms coreCheck462_18
end Erdos883Verified
