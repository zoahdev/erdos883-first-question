import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_25 :
    (List.ofFn coreChunks313_25).flatten =
      (coreData313.take (coreResources313 25).q).drop 61 := by
  decide +kernel

theorem coreCheck313_25 :
    ∀ c : Fin 1, (coreChunks313_25 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 25)) = true := by
  decide +kernel
#print axioms coreFlatten313_25
#print axioms coreCheck313_25
end Erdos883Verified
