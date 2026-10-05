import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_10 :
    (List.ofFn coreChunks234_10).flatten =
      (coreData234.take (coreResources234 10).q).drop 0 := by
  decide +kernel

theorem coreCheck234_10 :
    ∀ c : Fin 3, (coreChunks234_10 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 10)) = true := by
  decide +kernel
#print axioms coreFlatten234_10
#print axioms coreCheck234_10
end Erdos883Verified
