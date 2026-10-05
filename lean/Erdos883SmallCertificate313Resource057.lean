import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_57 :
    (List.ofFn coreChunks313_57).flatten =
      (coreData313.take (coreResources313 57).q).drop 0 := by
  decide +kernel

theorem coreCheck313_57 :
    ∀ c : Fin 6, (coreChunks313_57 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 57)) = true := by
  decide +kernel
#print axioms coreFlatten313_57
#print axioms coreCheck313_57
end Erdos883Verified
