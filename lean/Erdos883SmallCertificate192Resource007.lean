import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_7 :
    (List.ofFn coreChunks192_7).flatten =
      (coreData192.take (coreResources192 7).q).drop 47 := by
  decide +kernel

theorem coreCheck192_7 :
    ∀ c : Fin 1, (coreChunks192_7 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 7)) = true := by
  decide +kernel
#print axioms coreFlatten192_7
#print axioms coreCheck192_7
end Erdos883Verified
