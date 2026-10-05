import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_43 :
    (List.ofFn coreChunks234_43).flatten =
      (coreData234.take (coreResources234 43).q).drop 0 := by
  decide +kernel

theorem coreCheck234_43 :
    ∀ c : Fin 5, (coreChunks234_43 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 43)) = true := by
  decide +kernel
#print axioms coreFlatten234_43
#print axioms coreCheck234_43
end Erdos883Verified
