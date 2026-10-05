import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_21 :
    (List.ofFn coreChunks234_21).flatten =
      (coreData234.take (coreResources234 21).q).drop 51 := by
  decide +kernel

theorem coreCheck234_21 :
    ∀ c : Fin 1, (coreChunks234_21 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 21)) = true := by
  decide +kernel
#print axioms coreFlatten234_21
#print axioms coreCheck234_21
end Erdos883Verified
