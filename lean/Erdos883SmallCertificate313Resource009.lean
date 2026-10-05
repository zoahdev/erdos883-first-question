import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_9 :
    (List.ofFn coreChunks313_9).flatten =
      (coreData313.take (coreResources313 9).q).drop 70 := by
  decide +kernel

theorem coreCheck313_9 :
    ∀ c : Fin 1, (coreChunks313_9 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 9)) = true := by
  decide +kernel
#print axioms coreFlatten313_9
#print axioms coreCheck313_9
end Erdos883Verified
