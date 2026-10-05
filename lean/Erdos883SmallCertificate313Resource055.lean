import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_55 :
    (List.ofFn coreChunks313_55).flatten =
      (coreData313.take (coreResources313 55).q).drop 0 := by
  decide +kernel

theorem coreCheck313_55 :
    ∀ c : Fin 7, (coreChunks313_55 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 55)) = true := by
  decide +kernel
#print axioms coreFlatten313_55
#print axioms coreCheck313_55
end Erdos883Verified
