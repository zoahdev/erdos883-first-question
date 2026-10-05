import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_34 :
    (List.ofFn coreChunks234_34).flatten =
      (coreData234.take (coreResources234 34).q).drop 73 := by
  decide +kernel

theorem coreCheck234_34 :
    ∀ c : Fin 1, (coreChunks234_34 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 34)) = true := by
  decide +kernel
#print axioms coreFlatten234_34
#print axioms coreCheck234_34
end Erdos883Verified
