import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_3 :
    (List.ofFn coreChunks234_3).flatten =
      (coreData234.take (coreResources234 3).q).drop 32 := by
  decide +kernel

theorem coreCheck234_3 :
    ∀ c : Fin 2, (coreChunks234_3 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 3)) = true := by
  decide +kernel
#print axioms coreFlatten234_3
#print axioms coreCheck234_3
end Erdos883Verified
