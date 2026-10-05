import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_26 :
    (List.ofFn coreChunks313_26).flatten =
      (coreData313.take (coreResources313 26).q).drop 63 := by
  decide +kernel

theorem coreCheck313_26 :
    ∀ c : Fin 1, (coreChunks313_26 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 26)) = true := by
  decide +kernel
#print axioms coreFlatten313_26
#print axioms coreCheck313_26
end Erdos883Verified
