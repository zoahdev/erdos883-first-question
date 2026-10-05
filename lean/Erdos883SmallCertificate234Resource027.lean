import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_27 :
    (List.ofFn coreChunks234_27).flatten =
      (coreData234.take (coreResources234 27).q).drop 60 := by
  decide +kernel

theorem coreCheck234_27 :
    ∀ c : Fin 1, (coreChunks234_27 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 27)) = true := by
  decide +kernel
#print axioms coreFlatten234_27
#print axioms coreCheck234_27
end Erdos883Verified
