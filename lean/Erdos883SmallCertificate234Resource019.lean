import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_19 :
    (List.ofFn coreChunks234_19).flatten =
      (coreData234.take (coreResources234 19).q).drop 48 := by
  decide +kernel

theorem coreCheck234_19 :
    ∀ c : Fin 1, (coreChunks234_19 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 19)) = true := by
  decide +kernel
#print axioms coreFlatten234_19
#print axioms coreCheck234_19
end Erdos883Verified
