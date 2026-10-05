import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_12 :
    (List.ofFn coreChunks313_12).flatten =
      (coreData313.take (coreResources313 12).q).drop 74 := by
  decide +kernel

theorem coreCheck313_12 :
    ∀ c : Fin 1, (coreChunks313_12 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 12)) = true := by
  decide +kernel
#print axioms coreFlatten313_12
#print axioms coreCheck313_12
end Erdos883Verified
