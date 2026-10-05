import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_4 :
    (List.ofFn coreChunks462_4).flatten =
      (coreData462.take (coreResources462 4).q).drop 57 := by
  decide +kernel

theorem coreCheck462_4 :
    ∀ c : Fin 1, (coreChunks462_4 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 4)) = true := by
  decide +kernel
#print axioms coreFlatten462_4
#print axioms coreCheck462_4
end Erdos883Verified
