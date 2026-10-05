import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_37 :
    (List.ofFn coreChunks192_37).flatten =
      (coreData192.take (coreResources192 37).q).drop 62 := by
  decide +kernel

theorem coreCheck192_37 :
    ∀ c : Fin 1, (coreChunks192_37 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 37)) = true := by
  decide +kernel
#print axioms coreFlatten192_37
#print axioms coreCheck192_37
end Erdos883Verified
