import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_23 :
    (List.ofFn coreChunks234_23).flatten =
      (coreData234.take (coreResources234 23).q).drop 55 := by
  decide +kernel

theorem coreCheck234_23 :
    ∀ c : Fin 1, (coreChunks234_23 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 23)) = true := by
  decide +kernel
#print axioms coreFlatten234_23
#print axioms coreCheck234_23
end Erdos883Verified
