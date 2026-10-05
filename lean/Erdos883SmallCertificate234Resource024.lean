import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_24 :
    (List.ofFn coreChunks234_24).flatten =
      (coreData234.take (coreResources234 24).q).drop 56 := by
  decide +kernel

theorem coreCheck234_24 :
    ∀ c : Fin 1, (coreChunks234_24 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 24)) = true := by
  decide +kernel
#print axioms coreFlatten234_24
#print axioms coreCheck234_24
end Erdos883Verified
