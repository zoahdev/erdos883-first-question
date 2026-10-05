import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_2 :
    (List.ofFn coreChunks192_2).flatten =
      (coreData192.take (coreResources192 2).q).drop 22 := by
  decide +kernel

theorem coreCheck192_2 :
    ∀ c : Fin 1, (coreChunks192_2 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 2)) = true := by
  decide +kernel
#print axioms coreFlatten192_2
#print axioms coreCheck192_2
end Erdos883Verified
