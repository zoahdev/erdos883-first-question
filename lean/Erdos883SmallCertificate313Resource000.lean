import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_0 :
    (List.ofFn coreChunks313_0).flatten =
      (coreData313.take (coreResources313 0).q).drop 0 := by
  decide +kernel

theorem coreCheck313_0 :
    ∀ c : Fin 2, (coreChunks313_0 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 0)) = true := by
  decide +kernel
#print axioms coreFlatten313_0
#print axioms coreCheck313_0
end Erdos883Verified
