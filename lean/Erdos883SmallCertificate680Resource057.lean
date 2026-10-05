import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_57 :
    (List.ofFn coreChunks680_57).flatten =
      (coreData680.take (coreResources680 57).q).drop 113 := by
  decide +kernel

theorem coreCheck680_57 :
    ∀ c : Fin 1, (coreChunks680_57 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 57)) = true := by
  decide +kernel
#print axioms coreFlatten680_57
#print axioms coreCheck680_57
end Erdos883Verified
