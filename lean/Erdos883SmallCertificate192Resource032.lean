import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_32 :
    (List.ofFn coreChunks192_32).flatten =
      (coreData192.take (coreResources192 32).q).drop 72 := by
  decide +kernel

theorem coreCheck192_32 :
    ∀ c : Fin 1, (coreChunks192_32 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 32)) = true := by
  decide +kernel
#print axioms coreFlatten192_32
#print axioms coreCheck192_32
end Erdos883Verified
