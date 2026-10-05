import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_30 :
    (List.ofFn coreChunks192_30).flatten =
      (coreData192.take (coreResources192 30).q).drop 64 := by
  decide +kernel

theorem coreCheck192_30 :
    ∀ c : Fin 1, (coreChunks192_30 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 30)) = true := by
  decide +kernel
#print axioms coreFlatten192_30
#print axioms coreCheck192_30
end Erdos883Verified
