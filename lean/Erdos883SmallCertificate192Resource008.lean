import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_8 :
    (List.ofFn coreChunks192_8).flatten =
      (coreData192.take (coreResources192 8).q).drop 0 := by
  decide +kernel

theorem coreCheck192_8 :
    ∀ c : Fin 2, (coreChunks192_8 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 8)) = true := by
  decide +kernel
#print axioms coreFlatten192_8
#print axioms coreCheck192_8
end Erdos883Verified
