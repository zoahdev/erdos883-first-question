import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_32 :
    (List.ofFn coreChunks313_32).flatten =
      (coreData313.take (coreResources313 32).q).drop 72 := by
  decide +kernel

theorem coreCheck313_32 :
    ∀ c : Fin 1, (coreChunks313_32 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 32)) = true := by
  decide +kernel
#print axioms coreFlatten313_32
#print axioms coreCheck313_32
end Erdos883Verified
