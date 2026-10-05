import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_38 :
    (List.ofFn coreChunks234_38).flatten =
      (coreData234.take (coreResources234 38).q).drop 87 := by
  decide +kernel

theorem coreCheck234_38 :
    ∀ c : Fin 1, (coreChunks234_38 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 38)) = true := by
  decide +kernel
#print axioms coreFlatten234_38
#print axioms coreCheck234_38
end Erdos883Verified
