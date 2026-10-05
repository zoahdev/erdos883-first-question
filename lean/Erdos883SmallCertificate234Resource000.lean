import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_0 :
    (List.ofFn coreChunks234_0).flatten =
      (coreData234.take (coreResources234 0).q).drop 0 := by
  decide +kernel

theorem coreCheck234_0 :
    ∀ c : Fin 2, (coreChunks234_0 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 0)) = true := by
  decide +kernel
#print axioms coreFlatten234_0
#print axioms coreCheck234_0
end Erdos883Verified
