import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_5 :
    (List.ofFn coreChunks462_5).flatten =
      (coreData462.take (coreResources462 5).q).drop 61 := by
  decide +kernel

theorem coreCheck462_5 :
    ∀ c : Fin 2, (coreChunks462_5 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 5)) = true := by
  decide +kernel
#print axioms coreFlatten462_5
#print axioms coreCheck462_5
end Erdos883Verified
