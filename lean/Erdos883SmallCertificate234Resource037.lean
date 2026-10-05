import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_37 :
    (List.ofFn coreChunks234_37).flatten =
      (coreData234.take (coreResources234 37).q).drop 82 := by
  decide +kernel

theorem coreCheck234_37 :
    ∀ c : Fin 1, (coreChunks234_37 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 37)) = true := by
  decide +kernel
#print axioms coreFlatten234_37
#print axioms coreCheck234_37
end Erdos883Verified
