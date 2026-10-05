import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_42 :
    (List.ofFn coreChunks313_42).flatten =
      (coreData313.take (coreResources313 42).q).drop 92 := by
  decide +kernel

theorem coreCheck313_42 :
    ∀ c : Fin 1, (coreChunks313_42 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 42)) = true := by
  decide +kernel
#print axioms coreFlatten313_42
#print axioms coreCheck313_42
end Erdos883Verified
