import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_29 :
    (List.ofFn coreChunks313_29).flatten =
      (coreData313.take (coreResources313 29).q).drop 67 := by
  decide +kernel

theorem coreCheck313_29 :
    ∀ c : Fin 1, (coreChunks313_29 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 29)) = true := by
  decide +kernel
#print axioms coreFlatten313_29
#print axioms coreCheck313_29
end Erdos883Verified
