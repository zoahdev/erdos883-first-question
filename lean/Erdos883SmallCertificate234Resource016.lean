import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_16 :
    (List.ofFn coreChunks234_16).flatten =
      (coreData234.take (coreResources234 16).q).drop 44 := by
  decide +kernel

theorem coreCheck234_16 :
    ∀ c : Fin 1, (coreChunks234_16 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 16)) = true := by
  decide +kernel
#print axioms coreFlatten234_16
#print axioms coreCheck234_16
end Erdos883Verified
