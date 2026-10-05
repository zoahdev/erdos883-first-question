import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_47 :
    (List.ofFn coreChunks313_47).flatten =
      (coreData313.take (coreResources313 47).q).drop 105 := by
  decide +kernel

theorem coreCheck313_47 :
    ∀ c : Fin 1, (coreChunks313_47 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 47)) = true := by
  decide +kernel
#print axioms coreFlatten313_47
#print axioms coreCheck313_47
end Erdos883Verified
