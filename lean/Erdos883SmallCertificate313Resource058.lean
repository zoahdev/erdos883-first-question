import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_58 :
    (List.ofFn coreChunks313_58).flatten =
      (coreData313.take (coreResources313 58).q).drop 0 := by
  decide +kernel

theorem coreCheck313_58 :
    ∀ c : Fin 6, (coreChunks313_58 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 58)) = true := by
  decide +kernel
#print axioms coreFlatten313_58
#print axioms coreCheck313_58
end Erdos883Verified
