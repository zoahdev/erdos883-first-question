import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_3 :
    (List.ofFn coreChunks313_3).flatten =
      (coreData313.take (coreResources313 3).q).drop 42 := by
  decide +kernel

theorem coreCheck313_3 :
    ∀ c : Fin 1, (coreChunks313_3 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 3)) = true := by
  decide +kernel
#print axioms coreFlatten313_3
#print axioms coreCheck313_3
end Erdos883Verified
