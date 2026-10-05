import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_27 :
    (List.ofFn coreChunks192_27).flatten =
      (coreData192.take (coreResources192 27).q).drop 56 := by
  decide +kernel

theorem coreCheck192_27 :
    ∀ c : Fin 1, (coreChunks192_27 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 27)) = true := by
  decide +kernel
#print axioms coreFlatten192_27
#print axioms coreCheck192_27
end Erdos883Verified
