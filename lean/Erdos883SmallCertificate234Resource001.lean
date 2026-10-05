import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_1 :
    (List.ofFn coreChunks234_1).flatten =
      (coreData234.take (coreResources234 1).q).drop 25 := by
  decide +kernel

theorem coreCheck234_1 :
    ∀ c : Fin 1, (coreChunks234_1 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 1)) = true := by
  decide +kernel
#print axioms coreFlatten234_1
#print axioms coreCheck234_1
end Erdos883Verified
