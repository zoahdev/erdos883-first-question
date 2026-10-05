import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_8 :
    (List.ofFn coreChunks234_8).flatten =
      (coreData234.take (coreResources234 8).q).drop 56 := by
  decide +kernel

theorem coreCheck234_8 :
    ∀ c : Fin 1, (coreChunks234_8 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 8)) = true := by
  decide +kernel
#print axioms coreFlatten234_8
#print axioms coreCheck234_8
end Erdos883Verified
