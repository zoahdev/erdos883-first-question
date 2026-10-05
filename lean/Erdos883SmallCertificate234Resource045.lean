import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_45 :
    (List.ofFn coreChunks234_45).flatten =
      (coreData234.take (coreResources234 45).q).drop 0 := by
  decide +kernel

theorem coreCheck234_45 :
    ∀ c : Fin 4, (coreChunks234_45 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 45)) = true := by
  decide +kernel
#print axioms coreFlatten234_45
#print axioms coreCheck234_45
end Erdos883Verified
