import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_72 :
    (List.ofFn coreChunks680_72).flatten =
      (coreData680.take (coreResources680 72).q).drop 136 := by
  decide +kernel

theorem coreCheck680_72 :
    ∀ c : Fin 1, (coreChunks680_72 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 72)) = true := by
  decide +kernel
#print axioms coreFlatten680_72
#print axioms coreCheck680_72
end Erdos883Verified
