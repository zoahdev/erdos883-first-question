import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_26 :
    (List.ofFn coreChunks234_26).flatten =
      (coreData234.take (coreResources234 26).q).drop 59 := by
  decide +kernel

theorem coreCheck234_26 :
    ∀ c : Fin 1, (coreChunks234_26 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 26)) = true := by
  decide +kernel
#print axioms coreFlatten234_26
#print axioms coreCheck234_26
end Erdos883Verified
