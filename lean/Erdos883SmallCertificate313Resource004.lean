import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_4 :
    (List.ofFn coreChunks313_4).flatten =
      (coreData313.take (coreResources313 4).q).drop 43 := by
  decide +kernel

theorem coreCheck313_4 :
    ∀ c : Fin 2, (coreChunks313_4 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 4)) = true := by
  decide +kernel
#print axioms coreFlatten313_4
#print axioms coreCheck313_4
end Erdos883Verified
