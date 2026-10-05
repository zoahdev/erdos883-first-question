import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_38 :
    (List.ofFn coreChunks313_38).flatten =
      (coreData313.take (coreResources313 38).q).drop 82 := by
  decide +kernel

theorem coreCheck313_38 :
    ∀ c : Fin 1, (coreChunks313_38 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 38)) = true := by
  decide +kernel
#print axioms coreFlatten313_38
#print axioms coreCheck313_38
end Erdos883Verified
