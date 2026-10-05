import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_53 :
    (List.ofFn coreChunks680_53).flatten =
      (coreData680.take (coreResources680 53).q).drop 109 := by
  decide +kernel

theorem coreCheck680_53 :
    ∀ c : Fin 1, (coreChunks680_53 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 53)) = true := by
  decide +kernel
#print axioms coreFlatten680_53
#print axioms coreCheck680_53
end Erdos883Verified
