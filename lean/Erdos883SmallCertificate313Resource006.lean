import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_6 :
    (List.ofFn coreChunks313_6).flatten =
      (coreData313.take (coreResources313 6).q).drop 67 := by
  decide +kernel

theorem coreCheck313_6 :
    ∀ c : Fin 1, (coreChunks313_6 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 6)) = true := by
  decide +kernel
#print axioms coreFlatten313_6
#print axioms coreCheck313_6
end Erdos883Verified
