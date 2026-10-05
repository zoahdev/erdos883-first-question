import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_54 :
    (List.ofFn coreChunks313_54).flatten =
      (coreData313.take (coreResources313 54).q).drop 0 := by
  decide +kernel

theorem coreCheck313_54 :
    ∀ c : Fin 8, (coreChunks313_54 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 54)) = true := by
  decide +kernel
#print axioms coreFlatten313_54
#print axioms coreCheck313_54
end Erdos883Verified
