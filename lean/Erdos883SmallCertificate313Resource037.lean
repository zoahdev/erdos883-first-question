import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_37 :
    (List.ofFn coreChunks313_37).flatten =
      (coreData313.take (coreResources313 37).q).drop 81 := by
  decide +kernel

theorem coreCheck313_37 :
    ∀ c : Fin 1, (coreChunks313_37 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 37)) = true := by
  decide +kernel
#print axioms coreFlatten313_37
#print axioms coreCheck313_37
end Erdos883Verified
