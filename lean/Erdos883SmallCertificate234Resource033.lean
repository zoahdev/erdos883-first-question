import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_33 :
    (List.ofFn coreChunks234_33).flatten =
      (coreData234.take (coreResources234 33).q).drop 71 := by
  decide +kernel

theorem coreCheck234_33 :
    ∀ c : Fin 1, (coreChunks234_33 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 33)) = true := by
  decide +kernel
#print axioms coreFlatten234_33
#print axioms coreCheck234_33
end Erdos883Verified
