import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_18 :
    (List.ofFn coreChunks234_18).flatten =
      (coreData234.take (coreResources234 18).q).drop 46 := by
  decide +kernel

theorem coreCheck234_18 :
    ∀ c : Fin 1, (coreChunks234_18 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 18)) = true := by
  decide +kernel
#print axioms coreFlatten234_18
#print axioms coreCheck234_18
end Erdos883Verified
