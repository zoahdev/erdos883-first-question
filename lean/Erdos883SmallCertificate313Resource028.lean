import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_28 :
    (List.ofFn coreChunks313_28).flatten =
      (coreData313.take (coreResources313 28).q).drop 66 := by
  decide +kernel

theorem coreCheck313_28 :
    ∀ c : Fin 1, (coreChunks313_28 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 28)) = true := by
  decide +kernel
#print axioms coreFlatten313_28
#print axioms coreCheck313_28
end Erdos883Verified
