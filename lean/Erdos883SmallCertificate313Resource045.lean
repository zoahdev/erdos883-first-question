import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_45 :
    (List.ofFn coreChunks313_45).flatten =
      (coreData313.take (coreResources313 45).q).drop 98 := by
  decide +kernel

theorem coreCheck313_45 :
    ∀ c : Fin 1, (coreChunks313_45 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 45)) = true := by
  decide +kernel
#print axioms coreFlatten313_45
#print axioms coreCheck313_45
end Erdos883Verified
