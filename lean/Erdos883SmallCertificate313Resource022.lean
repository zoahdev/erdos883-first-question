import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_22 :
    (List.ofFn coreChunks313_22).flatten =
      (coreData313.take (coreResources313 22).q).drop 57 := by
  decide +kernel

theorem coreCheck313_22 :
    ∀ c : Fin 1, (coreChunks313_22 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 22)) = true := by
  decide +kernel
#print axioms coreFlatten313_22
#print axioms coreCheck313_22
end Erdos883Verified
