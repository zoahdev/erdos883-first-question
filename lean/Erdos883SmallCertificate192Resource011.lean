import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_11 :
    (List.ofFn coreChunks192_11).flatten =
      (coreData192.take (coreResources192 11).q).drop 31 := by
  decide +kernel

theorem coreCheck192_11 :
    ∀ c : Fin 1, (coreChunks192_11 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 11)) = true := by
  decide +kernel
#print axioms coreFlatten192_11
#print axioms coreCheck192_11
end Erdos883Verified
