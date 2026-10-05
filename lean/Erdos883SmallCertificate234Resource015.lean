import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_15 :
    (List.ofFn coreChunks234_15).flatten =
      (coreData234.take (coreResources234 15).q).drop 43 := by
  decide +kernel

theorem coreCheck234_15 :
    ∀ c : Fin 1, (coreChunks234_15 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 15)) = true := by
  decide +kernel
#print axioms coreFlatten234_15
#print axioms coreCheck234_15
end Erdos883Verified
