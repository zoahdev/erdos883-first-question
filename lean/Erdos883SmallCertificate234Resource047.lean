import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten234_47 :
    (List.ofFn coreChunks234_47).flatten =
      (coreData234.take (coreResources234 47).q).drop 67 := by
  decide +kernel

theorem coreCheck234_47 :
    ∀ c : Fin 1, (coreChunks234_47 c).all
      (coreResourceRowCheck 213 coreData234 (coreResources234 47)) = true := by
  decide +kernel
#print axioms coreFlatten234_47
#print axioms coreCheck234_47
end Erdos883Verified
