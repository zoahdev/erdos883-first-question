import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_5 :
    (List.ofFn coreChunks234_5).flatten =
      (coreData234.take (coreResources234 5).q).drop 52 := by
  decide +kernel

theorem coreCheck234_5 :
    ∀ c : Fin 1, (coreChunks234_5 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 5)) = true := by
  decide +kernel
#print axioms coreFlatten234_5
#print axioms coreCheck234_5
end Erdos883Verified
