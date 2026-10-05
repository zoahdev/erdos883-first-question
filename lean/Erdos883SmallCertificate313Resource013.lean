import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_13 :
    (List.ofFn coreChunks313_13).flatten =
      (coreData313.take (coreResources313 13).q).drop 77 := by
  decide +kernel

theorem coreCheck313_13 :
    ∀ c : Fin 1, (coreChunks313_13 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 13)) = true := by
  decide +kernel
#print axioms coreFlatten313_13
#print axioms coreCheck313_13
end Erdos883Verified
