import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_33 :
    (List.ofFn coreChunks462_33).flatten =
      (coreData462.take (coreResources462 33).q).drop 75 := by
  decide +kernel

theorem coreCheck462_33 :
    ∀ c : Fin 1, (coreChunks462_33 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 33)) = true := by
  decide +kernel
#print axioms coreFlatten462_33
#print axioms coreCheck462_33
end Erdos883Verified
