import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_35 :
    (List.ofFn coreChunks313_35).flatten =
      (coreData313.take (coreResources313 35).q).drop 77 := by
  decide +kernel

theorem coreCheck313_35 :
    ∀ c : Fin 1, (coreChunks313_35 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 35)) = true := by
  decide +kernel
#print axioms coreFlatten313_35
#print axioms coreCheck313_35
end Erdos883Verified
