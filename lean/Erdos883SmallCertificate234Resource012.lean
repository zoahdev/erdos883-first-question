import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_12 :
    (List.ofFn coreChunks234_12).flatten =
      (coreData234.take (coreResources234 12).q).drop 37 := by
  decide +kernel

theorem coreCheck234_12 :
    ∀ c : Fin 1, (coreChunks234_12 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 12)) = true := by
  decide +kernel
#print axioms coreFlatten234_12
#print axioms coreCheck234_12
end Erdos883Verified
