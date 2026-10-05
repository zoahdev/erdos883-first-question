import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_18 :
    (List.ofFn coreChunks313_18).flatten =
      (coreData313.take (coreResources313 18).q).drop 51 := by
  decide +kernel

theorem coreCheck313_18 :
    ∀ c : Fin 1, (coreChunks313_18 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 18)) = true := by
  decide +kernel
#print axioms coreFlatten313_18
#print axioms coreCheck313_18
end Erdos883Verified
