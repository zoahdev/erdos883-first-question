import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_2 :
    (List.ofFn coreChunks462_2).flatten =
      (coreData462.take (coreResources462 2).q).drop 45 := by
  decide +kernel

theorem coreCheck462_2 :
    ∀ c : Fin 1, (coreChunks462_2 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 2)) = true := by
  decide +kernel
#print axioms coreFlatten462_2
#print axioms coreCheck462_2
end Erdos883Verified
