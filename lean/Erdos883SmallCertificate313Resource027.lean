import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_27 :
    (List.ofFn coreChunks313_27).flatten =
      (coreData313.take (coreResources313 27).q).drop 65 := by
  decide +kernel

theorem coreCheck313_27 :
    ∀ c : Fin 1, (coreChunks313_27 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 27)) = true := by
  decide +kernel
#print axioms coreFlatten313_27
#print axioms coreCheck313_27
end Erdos883Verified
