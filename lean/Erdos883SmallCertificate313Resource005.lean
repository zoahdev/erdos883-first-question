import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_5 :
    (List.ofFn coreChunks313_5).flatten =
      (coreData313.take (coreResources313 5).q).drop 66 := by
  decide +kernel

theorem coreCheck313_5 :
    ∀ c : Fin 1, (coreChunks313_5 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 5)) = true := by
  decide +kernel
#print axioms coreFlatten313_5
#print axioms coreCheck313_5
end Erdos883Verified
