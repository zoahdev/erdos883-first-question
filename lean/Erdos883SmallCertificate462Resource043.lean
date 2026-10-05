import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_43 :
    (List.ofFn coreChunks462_43).flatten =
      (coreData462.take (coreResources462 43).q).drop 88 := by
  decide +kernel

theorem coreCheck462_43 :
    ∀ c : Fin 1, (coreChunks462_43 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 43)) = true := by
  decide +kernel
#print axioms coreFlatten462_43
#print axioms coreCheck462_43
end Erdos883Verified
