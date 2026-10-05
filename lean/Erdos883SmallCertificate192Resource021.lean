import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_21 :
    (List.ofFn coreChunks192_21).flatten =
      (coreData192.take (coreResources192 21).q).drop 46 := by
  decide +kernel

theorem coreCheck192_21 :
    ∀ c : Fin 1, (coreChunks192_21 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 21)) = true := by
  decide +kernel
#print axioms coreFlatten192_21
#print axioms coreCheck192_21
end Erdos883Verified
