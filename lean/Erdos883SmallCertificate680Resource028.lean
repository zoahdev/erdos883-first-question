import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_28 :
    (List.ofFn coreChunks680_28).flatten =
      (coreData680.take (coreResources680 28).q).drop 146 := by
  decide +kernel

theorem coreCheck680_28 :
    ∀ c : Fin 1, (coreChunks680_28 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 28)) = true := by
  decide +kernel
#print axioms coreFlatten680_28
#print axioms coreCheck680_28
end Erdos883Verified
