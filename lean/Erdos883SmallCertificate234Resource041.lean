import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_41 :
    (List.ofFn coreChunks234_41).flatten =
      (coreData234.take (coreResources234 41).q).drop 113 := by
  decide +kernel

theorem coreCheck234_41 :
    ∀ c : Fin 1, (coreChunks234_41 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 41)) = true := by
  decide +kernel
#print axioms coreFlatten234_41
#print axioms coreCheck234_41
end Erdos883Verified
