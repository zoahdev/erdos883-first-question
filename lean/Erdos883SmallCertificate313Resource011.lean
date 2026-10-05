import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_11 :
    (List.ofFn coreChunks313_11).flatten =
      (coreData313.take (coreResources313 11).q).drop 73 := by
  decide +kernel

theorem coreCheck313_11 :
    ∀ c : Fin 1, (coreChunks313_11 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 11)) = true := by
  decide +kernel
#print axioms coreFlatten313_11
#print axioms coreCheck313_11
end Erdos883Verified
