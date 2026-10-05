import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_31 :
    (List.ofFn coreChunks234_31).flatten =
      (coreData234.take (coreResources234 31).q).drop 67 := by
  decide +kernel

theorem coreCheck234_31 :
    ∀ c : Fin 1, (coreChunks234_31 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 31)) = true := by
  decide +kernel
#print axioms coreFlatten234_31
#print axioms coreCheck234_31
end Erdos883Verified
