import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_7 :
    (List.ofFn coreChunks234_7).flatten =
      (coreData234.take (coreResources234 7).q).drop 55 := by
  decide +kernel

theorem coreCheck234_7 :
    ∀ c : Fin 1, (coreChunks234_7 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 7)) = true := by
  decide +kernel
#print axioms coreFlatten234_7
#print axioms coreCheck234_7
end Erdos883Verified
