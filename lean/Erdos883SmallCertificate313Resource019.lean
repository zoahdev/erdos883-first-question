import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_19 :
    (List.ofFn coreChunks313_19).flatten =
      (coreData313.take (coreResources313 19).q).drop 52 := by
  decide +kernel

theorem coreCheck313_19 :
    ∀ c : Fin 1, (coreChunks313_19 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 19)) = true := by
  decide +kernel
#print axioms coreFlatten313_19
#print axioms coreCheck313_19
end Erdos883Verified
