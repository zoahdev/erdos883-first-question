import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_23 :
    (List.ofFn coreChunks313_23).flatten =
      (coreData313.take (coreResources313 23).q).drop 58 := by
  decide +kernel

theorem coreCheck313_23 :
    ∀ c : Fin 1, (coreChunks313_23 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 23)) = true := by
  decide +kernel
#print axioms coreFlatten313_23
#print axioms coreCheck313_23
end Erdos883Verified
