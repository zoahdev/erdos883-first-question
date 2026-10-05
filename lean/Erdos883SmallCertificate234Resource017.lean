import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_17 :
    (List.ofFn coreChunks234_17).flatten =
      (coreData234.take (coreResources234 17).q).drop 45 := by
  decide +kernel

theorem coreCheck234_17 :
    ∀ c : Fin 1, (coreChunks234_17 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 17)) = true := by
  decide +kernel
#print axioms coreFlatten234_17
#print axioms coreCheck234_17
end Erdos883Verified
