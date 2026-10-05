import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_22 :
    (List.ofFn coreChunks234_22).flatten =
      (coreData234.take (coreResources234 22).q).drop 54 := by
  decide +kernel

theorem coreCheck234_22 :
    ∀ c : Fin 1, (coreChunks234_22 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 22)) = true := by
  decide +kernel
#print axioms coreFlatten234_22
#print axioms coreCheck234_22
end Erdos883Verified
