import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_50 :
    (List.ofFn coreChunks462_50).flatten =
      (coreData462.take (coreResources462 50).q).drop 98 := by
  decide +kernel

theorem coreCheck462_50 :
    ∀ c : Fin 1, (coreChunks462_50 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 50)) = true := by
  decide +kernel
#print axioms coreFlatten462_50
#print axioms coreCheck462_50
end Erdos883Verified
