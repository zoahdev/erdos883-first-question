import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_46 :
    (List.ofFn coreChunks234_46).flatten =
      (coreData234.take (coreResources234 46).q).drop 0 := by
  decide +kernel

theorem coreCheck234_46 :
    ∀ c : Fin 5, (coreChunks234_46 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 46)) = true := by
  decide +kernel
#print axioms coreFlatten234_46
#print axioms coreCheck234_46
end Erdos883Verified
