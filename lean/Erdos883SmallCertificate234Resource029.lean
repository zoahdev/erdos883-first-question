import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_29 :
    (List.ofFn coreChunks234_29).flatten =
      (coreData234.take (coreResources234 29).q).drop 64 := by
  decide +kernel

theorem coreCheck234_29 :
    ∀ c : Fin 1, (coreChunks234_29 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 29)) = true := by
  decide +kernel
#print axioms coreFlatten234_29
#print axioms coreCheck234_29
end Erdos883Verified
