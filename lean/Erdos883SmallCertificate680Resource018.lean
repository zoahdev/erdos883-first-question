import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_18 :
    (List.ofFn coreChunks680_18).flatten =
      (coreData680.take (coreResources680 18).q).drop 133 := by
  decide +kernel

theorem coreCheck680_18 :
    ∀ c : Fin 1, (coreChunks680_18 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 18)) = true := by
  decide +kernel
#print axioms coreFlatten680_18
#print axioms coreCheck680_18
end Erdos883Verified
