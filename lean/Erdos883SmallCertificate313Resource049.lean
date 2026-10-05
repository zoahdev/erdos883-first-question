import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_49 :
    (List.ofFn coreChunks313_49).flatten =
      (coreData313.take (coreResources313 49).q).drop 117 := by
  decide +kernel

theorem coreCheck313_49 :
    ∀ c : Fin 1, (coreChunks313_49 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 49)) = true := by
  decide +kernel
#print axioms coreFlatten313_49
#print axioms coreCheck313_49
end Erdos883Verified
