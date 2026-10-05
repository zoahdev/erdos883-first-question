import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_40 :
    (List.ofFn coreChunks192_40).flatten =
      (coreData192.take (coreResources192 40).q).drop 52 := by
  decide +kernel

theorem coreCheck192_40 :
    ∀ c : Fin 1, (coreChunks192_40 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 40)) = true := by
  decide +kernel
#print axioms coreFlatten192_40
#print axioms coreCheck192_40
end Erdos883Verified
