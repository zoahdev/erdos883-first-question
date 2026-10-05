import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_56 :
    (List.ofFn coreChunks313_56).flatten =
      (coreData313.take (coreResources313 56).q).drop 102 := by
  decide +kernel

theorem coreCheck313_56 :
    ∀ c : Fin 1, (coreChunks313_56 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 56)) = true := by
  decide +kernel
#print axioms coreFlatten313_56
#print axioms coreCheck313_56
end Erdos883Verified
