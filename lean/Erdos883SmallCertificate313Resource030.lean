import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_30 :
    (List.ofFn coreChunks313_30).flatten =
      (coreData313.take (coreResources313 30).q).drop 68 := by
  decide +kernel

theorem coreCheck313_30 :
    ∀ c : Fin 1, (coreChunks313_30 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 30)) = true := by
  decide +kernel
#print axioms coreFlatten313_30
#print axioms coreCheck313_30
end Erdos883Verified
