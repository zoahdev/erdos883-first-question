import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_36 :
    (List.ofFn coreChunks462_36).flatten =
      (coreData462.take (coreResources462 36).q).drop 78 := by
  decide +kernel

theorem coreCheck462_36 :
    ∀ c : Fin 1, (coreChunks462_36 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 36)) = true := by
  decide +kernel
#print axioms coreFlatten462_36
#print axioms coreCheck462_36
end Erdos883Verified
