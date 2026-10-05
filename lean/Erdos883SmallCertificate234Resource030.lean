import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_30 :
    (List.ofFn coreChunks234_30).flatten =
      (coreData234.take (coreResources234 30).q).drop 65 := by
  decide +kernel

theorem coreCheck234_30 :
    ∀ c : Fin 1, (coreChunks234_30 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 30)) = true := by
  decide +kernel
#print axioms coreFlatten234_30
#print axioms coreCheck234_30
end Erdos883Verified
