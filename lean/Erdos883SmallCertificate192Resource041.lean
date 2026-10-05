import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_41 :
    (List.ofFn coreChunks192_41).flatten =
      (coreData192.take (coreResources192 41).q).drop 53 := by
  decide +kernel

theorem coreCheck192_41 :
    ∀ c : Fin 1, (coreChunks192_41 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 41)) = true := by
  decide +kernel
#print axioms coreFlatten192_41
#print axioms coreCheck192_41
end Erdos883Verified
