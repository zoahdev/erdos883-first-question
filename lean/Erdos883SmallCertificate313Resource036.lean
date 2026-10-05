import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_36 :
    (List.ofFn coreChunks313_36).flatten =
      (coreData313.take (coreResources313 36).q).drop 79 := by
  decide +kernel

theorem coreCheck313_36 :
    ∀ c : Fin 1, (coreChunks313_36 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 36)) = true := by
  decide +kernel
#print axioms coreFlatten313_36
#print axioms coreCheck313_36
end Erdos883Verified
