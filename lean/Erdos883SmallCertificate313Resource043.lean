import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_43 :
    (List.ofFn coreChunks313_43).flatten =
      (coreData313.take (coreResources313 43).q).drop 94 := by
  decide +kernel

theorem coreCheck313_43 :
    ∀ c : Fin 1, (coreChunks313_43 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 43)) = true := by
  decide +kernel
#print axioms coreFlatten313_43
#print axioms coreCheck313_43
end Erdos883Verified
