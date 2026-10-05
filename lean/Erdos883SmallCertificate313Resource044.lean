import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_44 :
    (List.ofFn coreChunks313_44).flatten =
      (coreData313.take (coreResources313 44).q).drop 96 := by
  decide +kernel

theorem coreCheck313_44 :
    ∀ c : Fin 1, (coreChunks313_44 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 44)) = true := by
  decide +kernel
#print axioms coreFlatten313_44
#print axioms coreCheck313_44
end Erdos883Verified
