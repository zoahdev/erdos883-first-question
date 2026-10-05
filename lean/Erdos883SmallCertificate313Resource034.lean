import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_34 :
    (List.ofFn coreChunks313_34).flatten =
      (coreData313.take (coreResources313 34).q).drop 74 := by
  decide +kernel

theorem coreCheck313_34 :
    ∀ c : Fin 1, (coreChunks313_34 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 34)) = true := by
  decide +kernel
#print axioms coreFlatten313_34
#print axioms coreCheck313_34
end Erdos883Verified
