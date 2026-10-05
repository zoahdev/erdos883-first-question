import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_13 :
    (List.ofFn coreChunks192_13).flatten =
      (coreData192.take (coreResources192 13).q).drop 35 := by
  decide +kernel

theorem coreCheck192_13 :
    ∀ c : Fin 1, (coreChunks192_13 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 13)) = true := by
  decide +kernel
#print axioms coreFlatten192_13
#print axioms coreCheck192_13
end Erdos883Verified
