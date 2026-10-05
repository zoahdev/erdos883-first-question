import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_11 :
    (List.ofFn coreChunks234_11).flatten =
      (coreData234.take (coreResources234 11).q).drop 36 := by
  decide +kernel

theorem coreCheck234_11 :
    ∀ c : Fin 1, (coreChunks234_11 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 11)) = true := by
  decide +kernel
#print axioms coreFlatten234_11
#print axioms coreCheck234_11
end Erdos883Verified
