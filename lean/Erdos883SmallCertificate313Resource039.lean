import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_39 :
    (List.ofFn coreChunks313_39).flatten =
      (coreData313.take (coreResources313 39).q).drop 85 := by
  decide +kernel

theorem coreCheck313_39 :
    ∀ c : Fin 1, (coreChunks313_39 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 39)) = true := by
  decide +kernel
#print axioms coreFlatten313_39
#print axioms coreCheck313_39
end Erdos883Verified
