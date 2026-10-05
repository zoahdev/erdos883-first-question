import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_32 :
    (List.ofFn coreChunks234_32).flatten =
      (coreData234.take (coreResources234 32).q).drop 69 := by
  decide +kernel

theorem coreCheck234_32 :
    ∀ c : Fin 1, (coreChunks234_32 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 32)) = true := by
  decide +kernel
#print axioms coreFlatten234_32
#print axioms coreCheck234_32
end Erdos883Verified
