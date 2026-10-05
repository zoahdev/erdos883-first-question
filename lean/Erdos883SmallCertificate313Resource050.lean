import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_50 :
    (List.ofFn coreChunks313_50).flatten =
      (coreData313.take (coreResources313 50).q).drop 126 := by
  decide +kernel

theorem coreCheck313_50 :
    ∀ c : Fin 1, (coreChunks313_50 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 50)) = true := by
  decide +kernel
#print axioms coreFlatten313_50
#print axioms coreCheck313_50
end Erdos883Verified
