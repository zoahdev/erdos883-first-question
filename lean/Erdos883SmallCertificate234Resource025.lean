import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_25 :
    (List.ofFn coreChunks234_25).flatten =
      (coreData234.take (coreResources234 25).q).drop 58 := by
  decide +kernel

theorem coreCheck234_25 :
    ∀ c : Fin 1, (coreChunks234_25 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 25)) = true := by
  decide +kernel
#print axioms coreFlatten234_25
#print axioms coreCheck234_25
end Erdos883Verified
