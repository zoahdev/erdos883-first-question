import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_10 :
    (List.ofFn coreChunks313_10).flatten =
      (coreData313.take (coreResources313 10).q).drop 72 := by
  decide +kernel

theorem coreCheck313_10 :
    ∀ c : Fin 1, (coreChunks313_10 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 10)) = true := by
  decide +kernel
#print axioms coreFlatten313_10
#print axioms coreCheck313_10
end Erdos883Verified
