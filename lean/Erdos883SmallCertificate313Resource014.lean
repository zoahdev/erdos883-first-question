import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_14 :
    (List.ofFn coreChunks313_14).flatten =
      (coreData313.take (coreResources313 14).q).drop 79 := by
  decide +kernel

theorem coreCheck313_14 :
    ∀ c : Fin 1, (coreChunks313_14 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 14)) = true := by
  decide +kernel
#print axioms coreFlatten313_14
#print axioms coreCheck313_14
end Erdos883Verified
