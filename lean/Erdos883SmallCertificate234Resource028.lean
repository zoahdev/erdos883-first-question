import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_28 :
    (List.ofFn coreChunks234_28).flatten =
      (coreData234.take (coreResources234 28).q).drop 61 := by
  decide +kernel

theorem coreCheck234_28 :
    ∀ c : Fin 1, (coreChunks234_28 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 28)) = true := by
  decide +kernel
#print axioms coreFlatten234_28
#print axioms coreCheck234_28
end Erdos883Verified
