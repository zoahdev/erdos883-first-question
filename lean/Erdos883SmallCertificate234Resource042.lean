import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_42 :
    (List.ofFn coreChunks234_42).flatten =
      (coreData234.take (coreResources234 42).q).drop 0 := by
  decide +kernel

theorem coreCheck234_42 :
    ∀ c : Fin 6, (coreChunks234_42 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 42)) = true := by
  decide +kernel
#print axioms coreFlatten234_42
#print axioms coreCheck234_42
end Erdos883Verified
