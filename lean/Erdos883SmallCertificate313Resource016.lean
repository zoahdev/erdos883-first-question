import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_16 :
    (List.ofFn coreChunks313_16).flatten =
      (coreData313.take (coreResources313 16).q).drop 46 := by
  decide +kernel

theorem coreCheck313_16 :
    ∀ c : Fin 1, (coreChunks313_16 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 16)) = true := by
  decide +kernel
#print axioms coreFlatten313_16
#print axioms coreCheck313_16
end Erdos883Verified
