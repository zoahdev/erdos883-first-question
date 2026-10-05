import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_44 :
    (List.ofFn coreChunks234_44).flatten =
      (coreData234.take (coreResources234 44).q).drop 76 := by
  decide +kernel

theorem coreCheck234_44 :
    ∀ c : Fin 1, (coreChunks234_44 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 44)) = true := by
  decide +kernel
#print axioms coreFlatten234_44
#print axioms coreCheck234_44
end Erdos883Verified
