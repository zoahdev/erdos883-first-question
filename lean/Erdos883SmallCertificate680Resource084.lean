import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_84 :
    (List.ofFn coreChunks680_84).flatten =
      (coreData680.take (coreResources680 84).q).drop 153 := by
  decide +kernel

theorem coreCheck680_84 :
    ∀ c : Fin 1, (coreChunks680_84 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 84)) = true := by
  decide +kernel
#print axioms coreFlatten680_84
#print axioms coreCheck680_84
end Erdos883Verified
