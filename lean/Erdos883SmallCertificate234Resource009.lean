import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_9 :
    (List.ofFn coreChunks234_9).flatten =
      (coreData234.take (coreResources234 9).q).drop 58 := by
  decide +kernel

theorem coreCheck234_9 :
    ∀ c : Fin 1, (coreChunks234_9 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 9)) = true := by
  decide +kernel
#print axioms coreFlatten234_9
#print axioms coreCheck234_9
end Erdos883Verified
