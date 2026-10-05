import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_40 :
    (List.ofFn coreChunks234_40).flatten =
      (coreData234.take (coreResources234 40).q).drop 100 := by
  decide +kernel

theorem coreCheck234_40 :
    ∀ c : Fin 1, (coreChunks234_40 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 40)) = true := by
  decide +kernel
#print axioms coreFlatten234_40
#print axioms coreCheck234_40
end Erdos883Verified
