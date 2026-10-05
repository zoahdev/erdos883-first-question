import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_24 :
    (List.ofFn coreChunks313_24).flatten =
      (coreData313.take (coreResources313 24).q).drop 59 := by
  decide +kernel

theorem coreCheck313_24 :
    ∀ c : Fin 1, (coreChunks313_24 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 24)) = true := by
  decide +kernel
#print axioms coreFlatten313_24
#print axioms coreCheck313_24
end Erdos883Verified
