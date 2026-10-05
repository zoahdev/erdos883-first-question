import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_90 :
    (List.ofFn coreChunks680_90).flatten =
      (coreData680.take (coreResources680 90).q).drop 168 := by
  decide +kernel

theorem coreCheck680_90 :
    ∀ c : Fin 1, (coreChunks680_90 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 90)) = true := by
  decide +kernel
#print axioms coreFlatten680_90
#print axioms coreCheck680_90
end Erdos883Verified
