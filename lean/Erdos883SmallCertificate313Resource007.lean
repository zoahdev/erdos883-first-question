import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_7 :
    (List.ofFn coreChunks313_7).flatten =
      (coreData313.take (coreResources313 7).q).drop 68 := by
  decide +kernel

theorem coreCheck313_7 :
    ∀ c : Fin 1, (coreChunks313_7 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 7)) = true := by
  decide +kernel
#print axioms coreFlatten313_7
#print axioms coreCheck313_7
end Erdos883Verified
