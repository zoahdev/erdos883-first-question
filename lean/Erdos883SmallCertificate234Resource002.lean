import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_2 :
    (List.ofFn coreChunks234_2).flatten =
      (coreData234.take (coreResources234 2).q).drop 26 := by
  decide +kernel

theorem coreCheck234_2 :
    ∀ c : Fin 1, (coreChunks234_2 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 2)) = true := by
  decide +kernel
#print axioms coreFlatten234_2
#print axioms coreCheck234_2
end Erdos883Verified
