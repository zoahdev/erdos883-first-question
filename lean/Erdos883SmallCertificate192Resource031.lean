import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_31 :
    (List.ofFn coreChunks192_31).flatten =
      (coreData192.take (coreResources192 31).q).drop 68 := by
  decide +kernel

theorem coreCheck192_31 :
    ∀ c : Fin 1, (coreChunks192_31 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 31)) = true := by
  decide +kernel
#print axioms coreFlatten192_31
#print axioms coreCheck192_31
end Erdos883Verified
