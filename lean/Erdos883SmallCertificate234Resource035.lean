import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_35 :
    (List.ofFn coreChunks234_35).flatten =
      (coreData234.take (coreResources234 35).q).drop 74 := by
  decide +kernel

theorem coreCheck234_35 :
    ∀ c : Fin 1, (coreChunks234_35 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 35)) = true := by
  decide +kernel
#print axioms coreFlatten234_35
#print axioms coreCheck234_35
end Erdos883Verified
