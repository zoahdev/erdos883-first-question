import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_2 :
    (List.ofFn coreChunks313_2).flatten =
      (coreData313.take (coreResources313 2).q).drop 33 := by
  decide +kernel

theorem coreCheck313_2 :
    ∀ c : Fin 1, (coreChunks313_2 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 2)) = true := by
  decide +kernel
#print axioms coreFlatten313_2
#print axioms coreCheck313_2
end Erdos883Verified
