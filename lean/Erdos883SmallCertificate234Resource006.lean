import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_6 :
    (List.ofFn coreChunks234_6).flatten =
      (coreData234.take (coreResources234 6).q).drop 54 := by
  decide +kernel

theorem coreCheck234_6 :
    ∀ c : Fin 1, (coreChunks234_6 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 6)) = true := by
  decide +kernel
#print axioms coreFlatten234_6
#print axioms coreCheck234_6
end Erdos883Verified
