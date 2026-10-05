import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_31 :
    (List.ofFn coreChunks313_31).flatten =
      (coreData313.take (coreResources313 31).q).drop 69 := by
  decide +kernel

theorem coreCheck313_31 :
    ∀ c : Fin 1, (coreChunks313_31 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 31)) = true := by
  decide +kernel
#print axioms coreFlatten313_31
#print axioms coreCheck313_31
end Erdos883Verified
