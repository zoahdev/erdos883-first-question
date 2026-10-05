import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_20 :
    (List.ofFn coreChunks234_20).flatten =
      (coreData234.take (coreResources234 20).q).drop 50 := by
  decide +kernel

theorem coreCheck234_20 :
    ∀ c : Fin 1, (coreChunks234_20 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 20)) = true := by
  decide +kernel
#print axioms coreFlatten234_20
#print axioms coreCheck234_20
end Erdos883Verified
