import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_1 :
    (List.ofFn coreChunks313_1).flatten =
      (coreData313.take (coreResources313 1).q).drop 32 := by
  decide +kernel

theorem coreCheck313_1 :
    ∀ c : Fin 1, (coreChunks313_1 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 1)) = true := by
  decide +kernel
#print axioms coreFlatten313_1
#print axioms coreCheck313_1
end Erdos883Verified
