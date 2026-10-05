import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_52 :
    (List.ofFn coreChunks462_52).flatten =
      (coreData462.take (coreResources462 52).q).drop 100 := by
  decide +kernel

theorem coreCheck462_52 :
    ∀ c : Fin 1, (coreChunks462_52 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 52)) = true := by
  decide +kernel
#print axioms coreFlatten462_52
#print axioms coreCheck462_52
end Erdos883Verified
