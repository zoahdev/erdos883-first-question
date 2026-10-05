import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_52 :
    (List.ofFn coreChunks313_52).flatten =
      (coreData313.take (coreResources313 52).q).drop 138 := by
  decide +kernel

theorem coreCheck313_52 :
    ∀ c : Fin 1, (coreChunks313_52 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 52)) = true := by
  decide +kernel
#print axioms coreFlatten313_52
#print axioms coreCheck313_52
end Erdos883Verified
