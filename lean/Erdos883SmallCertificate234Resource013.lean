import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_13 :
    (List.ofFn coreChunks234_13).flatten =
      (coreData234.take (coreResources234 13).q).drop 41 := by
  decide +kernel

theorem coreCheck234_13 :
    ∀ c : Fin 1, (coreChunks234_13 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 13)) = true := by
  decide +kernel
#print axioms coreFlatten234_13
#print axioms coreCheck234_13
end Erdos883Verified
