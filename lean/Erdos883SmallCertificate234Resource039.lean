import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_39 :
    (List.ofFn coreChunks234_39).flatten =
      (coreData234.take (coreResources234 39).q).drop 94 := by
  decide +kernel

theorem coreCheck234_39 :
    ∀ c : Fin 1, (coreChunks234_39 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 39)) = true := by
  decide +kernel
#print axioms coreFlatten234_39
#print axioms coreCheck234_39
end Erdos883Verified
