import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_19 :
    (List.ofFn coreChunks462_19).flatten =
      (coreData462.take (coreResources462 19).q).drop 103 := by
  decide +kernel

theorem coreCheck462_19 :
    ∀ c : Fin 1, (coreChunks462_19 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 19)) = true := by
  decide +kernel
#print axioms coreFlatten462_19
#print axioms coreCheck462_19
end Erdos883Verified
