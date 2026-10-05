import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_42 :
    (List.ofFn coreChunks680_42).flatten =
      (coreData680.take (coreResources680 42).q).drop 168 := by
  decide +kernel

theorem coreCheck680_42 :
    ∀ c : Fin 1, (coreChunks680_42 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 42)) = true := by
  decide +kernel
#print axioms coreFlatten680_42
#print axioms coreCheck680_42
end Erdos883Verified
