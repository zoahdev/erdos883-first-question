import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_40 :
    (List.ofFn coreChunks313_40).flatten =
      (coreData313.take (coreResources313 40).q).drop 86 := by
  decide +kernel

theorem coreCheck313_40 :
    ∀ c : Fin 1, (coreChunks313_40 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 40)) = true := by
  decide +kernel
#print axioms coreFlatten313_40
#print axioms coreCheck313_40
end Erdos883Verified
