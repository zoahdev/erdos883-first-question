import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_51 :
    (List.ofFn coreChunks313_51).flatten =
      (coreData313.take (coreResources313 51).q).drop 134 := by
  decide +kernel

theorem coreCheck313_51 :
    ∀ c : Fin 1, (coreChunks313_51 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 51)) = true := by
  decide +kernel
#print axioms coreFlatten313_51
#print axioms coreCheck313_51
end Erdos883Verified
