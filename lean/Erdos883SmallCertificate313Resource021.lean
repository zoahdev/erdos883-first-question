import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_21 :
    (List.ofFn coreChunks313_21).flatten =
      (coreData313.take (coreResources313 21).q).drop 56 := by
  decide +kernel

theorem coreCheck313_21 :
    ∀ c : Fin 1, (coreChunks313_21 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 21)) = true := by
  decide +kernel
#print axioms coreFlatten313_21
#print axioms coreCheck313_21
end Erdos883Verified
