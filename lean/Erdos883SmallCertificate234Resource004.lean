import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_4 :
    (List.ofFn coreChunks234_4).flatten =
      (coreData234.take (coreResources234 4).q).drop 51 := by
  decide +kernel

theorem coreCheck234_4 :
    ∀ c : Fin 1, (coreChunks234_4 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 4)) = true := by
  decide +kernel
#print axioms coreFlatten234_4
#print axioms coreCheck234_4
end Erdos883Verified
