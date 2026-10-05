import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_17 :
    (List.ofFn coreChunks313_17).flatten =
      (coreData313.take (coreResources313 17).q).drop 47 := by
  decide +kernel

theorem coreCheck313_17 :
    ∀ c : Fin 1, (coreChunks313_17 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 17)) = true := by
  decide +kernel
#print axioms coreFlatten313_17
#print axioms coreCheck313_17
end Erdos883Verified
