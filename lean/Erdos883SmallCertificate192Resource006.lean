import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_6 :
    (List.ofFn coreChunks192_6).flatten =
      (coreData192.take (coreResources192 6).q).drop 46 := by
  decide +kernel

theorem coreCheck192_6 :
    ∀ c : Fin 1, (coreChunks192_6 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 6)) = true := by
  decide +kernel
#print axioms coreFlatten192_6
#print axioms coreCheck192_6
end Erdos883Verified
