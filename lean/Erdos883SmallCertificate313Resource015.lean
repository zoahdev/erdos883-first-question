import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_15 :
    (List.ofFn coreChunks313_15).flatten =
      (coreData313.take (coreResources313 15).q).drop 0 := by
  decide +kernel

theorem coreCheck313_15 :
    ∀ c : Fin 3, (coreChunks313_15 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 15)) = true := by
  decide +kernel
#print axioms coreFlatten313_15
#print axioms coreCheck313_15
end Erdos883Verified
