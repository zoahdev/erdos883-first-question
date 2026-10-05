import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_106 :
    (List.ofFn coreChunks680_106).flatten =
      (coreData680.take (coreResources680 106).q).drop 207 := by
  decide +kernel

theorem coreCheck680_106 :
    ∀ c : Fin 1, (coreChunks680_106 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 106)) = true := by
  decide +kernel
#print axioms coreFlatten680_106
#print axioms coreCheck680_106
end Erdos883Verified
