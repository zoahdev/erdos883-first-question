import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_123 :
    (List.ofFn coreChunks680_123).flatten =
      (coreData680.take (coreResources680 123).q).drop 292 := by
  decide +kernel

theorem coreCheck680_123 :
    ∀ c : Fin 1, (coreChunks680_123 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 123)) = true := by
  decide +kernel
#print axioms coreFlatten680_123
#print axioms coreCheck680_123
end Erdos883Verified
