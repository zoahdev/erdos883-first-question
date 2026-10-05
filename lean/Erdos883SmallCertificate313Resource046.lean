import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_46 :
    (List.ofFn coreChunks313_46).flatten =
      (coreData313.take (coreResources313 46).q).drop 99 := by
  decide +kernel

theorem coreCheck313_46 :
    ∀ c : Fin 1, (coreChunks313_46 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 46)) = true := by
  decide +kernel
#print axioms coreFlatten313_46
#print axioms coreCheck313_46
end Erdos883Verified
