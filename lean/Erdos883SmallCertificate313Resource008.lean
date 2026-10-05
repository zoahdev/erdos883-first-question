import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_8 :
    (List.ofFn coreChunks313_8).flatten =
      (coreData313.take (coreResources313 8).q).drop 69 := by
  decide +kernel

theorem coreCheck313_8 :
    ∀ c : Fin 1, (coreChunks313_8 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 8)) = true := by
  decide +kernel
#print axioms coreFlatten313_8
#print axioms coreCheck313_8
end Erdos883Verified
