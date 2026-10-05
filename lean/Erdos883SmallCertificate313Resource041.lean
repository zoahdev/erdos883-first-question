import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_41 :
    (List.ofFn coreChunks313_41).flatten =
      (coreData313.take (coreResources313 41).q).drop 89 := by
  decide +kernel

theorem coreCheck313_41 :
    ∀ c : Fin 1, (coreChunks313_41 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 41)) = true := by
  decide +kernel
#print axioms coreFlatten313_41
#print axioms coreCheck313_41
end Erdos883Verified
