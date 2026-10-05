import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_40 :
    (List.ofFn coreChunks462_40).flatten =
      (coreData462.take (coreResources462 40).q).drop 82 := by
  decide +kernel

theorem coreCheck462_40 :
    ∀ c : Fin 1, (coreChunks462_40 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 40)) = true := by
  decide +kernel
#print axioms coreFlatten462_40
#print axioms coreCheck462_40
end Erdos883Verified
