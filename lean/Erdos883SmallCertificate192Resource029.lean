import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_29 :
    (List.ofFn coreChunks192_29).flatten =
      (coreData192.take (coreResources192 29).q).drop 60 := by
  decide +kernel

theorem coreCheck192_29 :
    ∀ c : Fin 1, (coreChunks192_29 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 29)) = true := by
  decide +kernel
#print axioms coreFlatten192_29
#print axioms coreCheck192_29
end Erdos883Verified
